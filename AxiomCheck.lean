import LatticePrepro

/-!
# Axiom check

Pins the axioms used by the main theorems listed in the README. Each `#guard_msgs` fails the
build if the `#print axioms` output changes, e.g. if a proof starts depending on `sorryAx` or on
an additional axiom.
-/

/--
info: 'LatticePrepro.FixedSystem.isGapReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.FixedSystem.isGapReduction

/--
info: 'LatticePrepro.exists_explicit_momentRepresentation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.exists_explicit_momentRepresentation

/--
info: 'LatticePrepro.exists_gapReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.exists_gapReduction

/--
info: 'LatticePrepro.exists_code_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.exists_code_gap

/--
info: 'LatticePrepro.exists_lattice_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.exists_lattice_gap

/--
info: 'LatticePrepro.GateVerifier.language_toQuadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.GateVerifier.language_toQuadratic

/--
info: 'LatticePrepro.BoolCircuit.language_toGateVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.BoolCircuit.language_toGateVerifier
