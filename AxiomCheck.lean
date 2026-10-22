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
info: 'LatticePrepro.exists_latticeReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.exists_latticeReduction

/--
info: 'LatticePrepro.code_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.code_gap

/--
info: 'LatticePrepro.lattice_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.lattice_gap

/--
info: 'LatticePrepro.exists_code_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.exists_code_gap

/--
info: 'LatticePrepro.exists_lattice_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.exists_lattice_gap

/--
info: 'LatticePrepro.ThreeSAT.mem_language_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.ThreeSAT.mem_language_iff

/--
info: 'LatticePrepro.ThreeSAT.exists_code_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.ThreeSAT.exists_code_gap

/--
info: 'LatticePrepro.ThreeSAT.exists_lattice_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.ThreeSAT.exists_lattice_gap

/--
info: 'LatticePrepro.LatticeReduction.accepts_of_isApprox' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.LatticeReduction.accepts_of_isApprox

/--
info: 'LatticePrepro.LatticeFamily.latticeDist_eq_infDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.LatticeFamily.latticeDist_eq_infDist

/--
info: 'LatticePrepro.LatticeFamily.isZLattice_realLattice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.LatticeFamily.isZLattice_realLattice

/--
info: 'LatticePrepro.GateVerifier.language_toQuadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.GateVerifier.language_toQuadratic

/--
info: 'LatticePrepro.BoolCircuit.language_toGateVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LatticePrepro.BoolCircuit.language_toGateVerifier
