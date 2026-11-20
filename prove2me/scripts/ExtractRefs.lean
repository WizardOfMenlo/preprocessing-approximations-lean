/-
Stage 2b: every source reference to a project constant.

Run from `prove2me/workspace`:
  lake env lean --run ../scripts/ExtractRefs.lean LatticePrepro/Basic/Blocks.lean
Elaborates the file with info trees and prints one JSON object per identifier that resolves to
a constant declared in a `LatticePrepro.*` module (or in the file itself): its byte position and
the constant.

Proof terms do not record everything a proof needs to compile: a lemma that `simp` applies by
`rfl`, or a definition that is only unfolded, leaves no trace in the term. The source does.
-/
import Lean
open Lean Elab

unsafe def main (args : List String) : IO UInt32 := do
  let file := args[0]!
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx
  let opts : Options := ({} : Options).setBool `autoImplicit false
  let cmdState := Command.mkState env messages opts
  let cmdState := { cmdState with infoState := { cmdState.infoState with enabled := true } }
  let s ← IO.processCommands inputCtx parserState cmdState
  let finalEnv := s.commandState.env
  let modNames := finalEnv.header.moduleNames
  let isProj (n : Name) : Bool :=
    match finalEnv.getModuleIdxFor? n with
    | some idx => (`LatticePrepro).isPrefixOf modNames[idx.toNat]!
    | none => finalEnv.contains n
  let mut out : Array String := #[]
  for tree in s.commandState.infoState.trees do
    let refs := tree.foldInfo (init := (#[] : Array (Nat × Name))) fun _ info acc =>
      match info with
      | .ofTermInfo ti =>
        match ti.expr.consumeMData, ti.stx.getPos? (canonicalOnly := false) with
        | .const n _, some pos => if isProj n then acc.push (pos.byteIdx, n) else acc
        | _, _ => acc
      | _ => acc
    for (pos, n) in refs do
      out := out.push (Json.mkObj [("pos", Json.num pos), ("name", Json.str (toString n))]).compress
  IO.println (String.intercalate "\n" out.toList)
  let mut bad := false
  for msg in s.commandState.messages.toList do
    if msg.severity == .error then
      bad := true
      IO.eprintln s!"{file}: {← msg.toString}"
  return if bad then 1 else 0
