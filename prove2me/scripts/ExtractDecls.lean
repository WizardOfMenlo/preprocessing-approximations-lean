/-
Stage 1: the declaration graph of the (ported, built) `LatticePrepro` library.

Run from `prove2me/workspace`:
  lake env lean ../scripts/ExtractDecls.lean
Writes `../out/decl_graph.jsonl`, one JSON object per constant declared in a `LatticePrepro.*`
module: its kind, source range, and the project constants used by its type and by its value.
Only reads the elaborated environment.
-/
import LatticePrepro
open Lean Meta

/-- The leading `∀` binders of a type (syntactic, no unfolding). -/
partial def leadingBinders (e : Expr) (acc : Array Json := #[]) : Array Json :=
  match e with
  | .mdata _ b => leadingBinders b acc
  | .forallE n _ b bi =>
    let bis := match bi with
      | .default => "explicit" | .implicit => "implicit"
      | .strictImplicit => "strict" | .instImplicit => "inst"
    leadingBinders b (acc.push (Json.mkObj [
      ("name", Json.str (toString n)), ("bi", Json.str bis),
      ("hyg", Json.bool (n.hasMacroScopes || n.isAnonymous || n.isInternal))]))
  | _ => acc

run_meta do
  let env ← getEnv
  let projPrefix := `LatticePrepro
  let modNames := env.header.moduleNames
  let getMod (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).bind fun idx => modNames[idx.toNat]?
  let isProj (n : Name) : Bool :=
    match getMod n with
    | some m => projPrefix.isPrefixOf m
    | none => false
  let consts : Array (Name × ConstantInfo) :=
    env.constants.fold (init := #[]) fun acc n ci => if isProj n then acc.push (n, ci) else acc
  let mut lines : Array String := #[]
  for (n, ci) in consts do
    let some m := getMod n | continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let usedT := ci.type.getUsedConstants.filter isProj
    let usedV := (match ci with
      | .thmInfo t => t.value.getUsedConstants
      | .defnInfo d => d.value.getUsedConstants
      | .opaqueInfo o => o.value.getUsedConstants
      | .inductInfo i => i.ctors.toArray
      | _ => #[]).filter isProj
    let range ← findDeclarationRanges? n
    let rj := match range with
      | some r => Json.arr #[r.range.pos.line, r.range.pos.column, r.range.endPos.line,
          r.range.endPos.column]
      | none => Json.null
    let isInst ← Lean.Meta.isInstance n
    let hasDoc := (← findDocString? env n).isSome
    let binders := match ci with
      | .thmInfo _ => Json.arr (leadingBinders ci.type)
      | _ => Json.null
    let obj := Json.mkObj [
      ("name", Json.str (toString n)), ("module", Json.str (toString m)), ("kind", Json.str kind),
      ("internal", Json.bool n.isInternal), ("isInstance", Json.bool isInst),
      ("hasDoc", Json.bool hasDoc), ("range", rj),
      ("levelParams", Json.num ci.levelParams.length), ("binders", binders),
      ("typeDeps", Json.arr (usedT.map fun d => Json.str (toString d))),
      ("valueDeps", Json.arr (usedV.map fun d => Json.str (toString d)))]
    lines := lines.push obj.compress
  IO.FS.writeFile "../out/decl_graph.jsonl" (String.intercalate "\n" lines.toList ++ "\n")
  logInfo m!"wrote {lines.size} declarations"
