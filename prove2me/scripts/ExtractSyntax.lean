/-
Stage 2: source positions of every top-level command of one file.

Run from `prove2me/workspace`:
  lake env lean --run ../scripts/ExtractSyntax.lean LatticePrepro/Basic/Blocks.lean LatticePrepro.Basic.Blocks
Prints one JSON object per command: its syntax kind and byte range and, for declarations, the
positions of the keyword, the name, the docstring and the body, the signature binders, and the
number of leading `∀`/`→` binders of the stated type.

The file is only parsed. Scope commands (`namespace`, `section`, `end`, `open`) are elaborated so
that scoped notations are active where they are in the real build; the environment is the one
of the compiled module, so every namespace of the file already exists.
-/
import Lean
open Lean Elab Parser

partial def findFirst? (stx : Syntax) (p : Syntax → Bool) : Option Syntax :=
  if p stx then some stx else stx.getArgs.findSome? (findFirst? · p)

def rangeJson (stx : Syntax) : Json :=
  match stx.getPos? (canonicalOnly := false), stx.getTailPos? (canonicalOnly := false) with
  | some a, some b => Json.arr #[a.byteIdx, b.byteIdx]
  | _, _ => Json.null

def posJson (stx : Syntax) : Json :=
  match stx.getPos? (canonicalOnly := false) with
  | some a => Json.num a.byteIdx
  | none => Json.null

def isBracketed (k : SyntaxNodeKind) : Bool :=
  k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder ||
    k == ``Lean.Parser.Term.strictImplicitBinder

/-- Names bound by one binder (`"_"` for anonymous ones). -/
def binderNames (b : Syntax) : Array String :=
  let k := b.getKind
  if isBracketed k then
    b[1].getArgs.map fun i => if i.isIdent then toString i.getId else "_"
  else if k == ``Lean.Parser.Term.instBinder then
    match findFirst? b[1] (·.isIdent) with
    | some i => #[toString i.getId]
    | none => #["_"]
  else if b.isIdent then #[toString b.getId]
  else #["_"]

/-- Number of leading `∀`/`→` binders of a type, read off the syntax. -/
partial def leadCount (t : Syntax) : Nat :=
  let k := t.getKind
  if k == ``Lean.Parser.Term.paren then leadCount t[1]
  else if k == ``Lean.Parser.Term.arrow then 1 + leadCount t[2]
  else if k == ``Lean.Parser.Term.depArrow then (binderNames t[0]).size + leadCount t[2]
  else if k == ``Lean.Parser.Term.forall then
    t[1].getArgs.foldl (fun acc b => acc + (binderNames b).size) 0 + leadCount t[4]
  else if (toString k).startsWith "Lean.«term∀" || (toString k).startsWith "«term∀" then
    -- `∀ x ∈ s, p` and friends: one variable and one hypothesis
    2 + leadCount (t[t.getNumArgs - 1])
  else 0

def declValKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.declValSimple, ``Lean.Parser.Command.declValEqns,
   ``Lean.Parser.Command.whereStructInst]

def scopeKinds : List SyntaxNodeKind :=
  [``Lean.Parser.Command.namespace, ``Lean.Parser.Command.section, ``Lean.Parser.Command.end,
   ``Lean.Parser.Command.open]

/-- Facts about a declaration (`mods` = its `declModifiers`, `d` = the declaration proper). -/
def declFacts (mods d : Syntax) : List (String × Json) :=
  let declId := findFirst? d (·.getKind == ``Lean.Parser.Command.declId)
  let val := findFirst? d (declValKinds.contains ·.getKind)
  let sig := findFirst? d (·.getKind == ``Lean.Parser.Command.declSig)
  let sigFacts : List (String × Json) := match sig with
    | some s =>
      let names := s[0].getArgs.foldl (fun acc b => acc ++ binderNames b) #[]
      let ty := s[1][1]
      [("sigBinders", Json.arr (names.map Json.str)), ("conclLead", Json.num (leadCount ty)),
       ("typeHeadKind", Json.str (toString ty.getKind)), ("typeRange", rangeJson ty)]
    | none => []
  [("decl", Json.bool true), ("kw", Json.str (toString d.getKind)), ("kwPos", posJson d),
   ("doc", if mods[0].getNumArgs > 0 then rangeJson mods[0] else Json.null),
   ("attrs", if mods[1].getNumArgs > 0 then rangeJson mods[1] else Json.null),
   ("visibility", if mods[2].getNumArgs > 0 then rangeJson mods[2] else Json.null),
   ("declId", match declId with | some i => rangeJson i[0] | none => Json.null),
   ("declIdFull", match declId with | some i => rangeJson i | none => Json.null),
   ("valStart", match val with | some v => posJson v | none => Json.null)] ++ sigFacts

/-- Unwrap `cmd₁ in cmd₂`, collecting the ranges of the prefixes. -/
partial def unwrapIn (cmd : Syntax) (pre : Array Json := #[]) : Syntax × Array Json :=
  if cmd.getKind == ``Lean.Parser.Command.in then unwrapIn cmd[2] (pre.push (rangeJson cmd[0]))
  else (cmd, pre)

partial def collectIdents (stx : Syntax) (acc : Array Name := #[]) : Array Name :=
  if stx.isIdent then acc.push stx.getId else stx.getArgs.foldl (fun a s => collectIdents s a) acc

/-- The `open` commands of a command: itself, or its `open ... in` prefixes. -/
partial def openNodes (cmd : Syntax) (acc : Array Syntax := #[]) : Array Syntax :=
  if cmd.getKind == ``Lean.Parser.Command.in then
    openNodes cmd[2] (if cmd[0].getKind == ``Lean.Parser.Command.open then acc.push cmd[0] else acc)
  else if cmd.getKind == ``Lean.Parser.Command.open then acc.push cmd
  else acc

def cmdJson (cmd : Syntax) (opened : Array Name) : Json :=
  let (inner, pre) := unwrapIn cmd
  let k := inner.getKind
  let base : List (String × Json) :=
    [("kind", Json.str (toString k)), ("range", rangeJson cmd), ("inPrefixes", Json.arr pre),
     ("openResolved", Json.arr (opened.map fun n => Json.str (toString n)))]
  let extra : List (String × Json) :=
    if k == ``Lean.Parser.Command.declaration then declFacts inner[0] inner[1]
    else if k == `lemma then declFacts inner[0] inner[1]
    else if k == ``Lean.Parser.Command.namespace then [("name", Json.str (toString inner[1].getId))]
    else if k == ``Lean.Parser.Command.section || k == ``Lean.Parser.Command.end then
      [("name", match findFirst? inner (·.isIdent) with
        | some i => Json.str (toString i.getId) | none => Json.null)]
    else []
  Json.mkObj (base ++ extra)

partial def loop (acc : Array (Syntax × Array Name)) :
    Frontend.FrontendM (Array (Syntax × Array Name)) := do
  let cmdState ← Frontend.getCommandState
  let ictx ← Frontend.getInputContext
  let pstate ← Frontend.getParserState
  let scope := cmdState.scopes.head!
  let pmctx : ParserModuleContext :=
    { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls }
  let (cmd, ps, messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
  Frontend.setParserState ps
  Frontend.setMessages messages
  if Parser.isTerminalCommand cmd then return acc
  -- the namespaces that the `open`s of this command resolve to, in the current scope
  let opened := (openNodes cmd).foldl (init := (#[] : Array Name)) fun a o =>
    (collectIdents o).foldl (init := a) fun a id =>
      a ++ (ResolveName.resolveNamespace cmdState.env scope.currNamespace scope.openDecls id).toArray
  if scopeKinds.contains cmd.getKind then
    try Frontend.runCommandElabM (Command.elabCommand cmd) catch _ => pure ()
  loop (acc.push (cmd, opened))

unsafe def main (args : List String) : IO UInt32 := do
  let file := args[0]!
  let modName := args[1]!.toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let env ← importModules #[{ module := modName }] {} (trustLevel := 1024) (loadExts := true)
  let cmdState := Command.mkState env messages {}
  let (cmds, st) ← (loop #[]).run { inputCtx } |>.run
    { commandState := cmdState, parserState, cmdPos := parserState.pos }
  IO.println (Json.mkObj [("kind", Json.str "header"), ("range", rangeJson header)]).compress
  for (cmd, opened) in cmds do
    IO.println (cmdJson cmd opened).compress
  -- parse errors would make every later position unreliable: report them
  let mut bad := false
  for msg in st.commandState.messages.toList do
    if msg.severity == .error then
      bad := true
      IO.eprintln s!"{file}: {← msg.toString}"
  return if bad then 1 else 0
