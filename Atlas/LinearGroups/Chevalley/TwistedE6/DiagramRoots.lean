import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramLattice
import Atlas.LinearGroups.Chevalley.RootData.E6

/-! The diagram involution of the actual E6 root pairing, with both the
original lattice labels and the public Chevalley simple-node labels explicit. -/
namespace Atlas.Chevalley.TwistedE6
open E6Data

def rootDiagram : Equiv.Perm Root where
  toFun a := ⟨latticeDiagram ℤ a.val, (latticeDiagram_norm ℤ a.val).trans a.property⟩
  invFun a := ⟨latticeDiagram ℤ a.val, (latticeDiagram_norm ℤ a.val).trans a.property⟩
  left_inv a := Subtype.ext (latticeDiagram_involutive ℤ a.val)
  right_inv a := Subtype.ext (latticeDiagram_involutive ℤ a.val)

@[simp] theorem rootDiagram_val (a : Root) :
    (rootDiagram a).val = latticeDiagram ℤ a.val := rfl

theorem rootDiagram_involutive : Function.Involutive rootDiagram := by
  intro a
  exact Subtype.ext (latticeDiagram_involutive ℤ a.val)

theorem rootDiagram_simple (i : Fin 6) :
    rootDiagram (simpleRoot i) = simpleRoot (latticeNode i) :=
  Subtype.ext (latticeDiagram_single ℤ i 1)

theorem rootDiagram_polar (a b : Root) :
    polar (rootDiagram a).val (rootDiagram b).val = polar a.val b.val :=
  latticeDiagram_polar ℤ a.val b.val

theorem rootDiagram_reflect (a : Root) (x : Lattice) :
    latticeDiagram ℤ (reflect a x) = reflect (rootDiagram a) (latticeDiagram ℤ x) := by
  have hp : polar (latticeDiagram ℤ a.val) (latticeDiagram ℤ x) = polar a.val x :=
    latticeDiagram_polar ℤ a.val x
  simp only [reflect, map_sub, map_smul, rootDiagram_val, hp]

theorem rootDiagram_reflectionPerm (a b : Root) :
    rootDiagram (reflectionPerm a b) = reflectionPerm (rootDiagram a) (rootDiagram b) :=
  Subtype.ext (rootDiagram_reflect a b.val)

/-- Diagram symmetry expressed in the already public mathlib node numbering. -/
def simpleNode : Equiv.Perm (Fin 6) :=
  nodeEquiv.symm.trans (latticeNode.trans nodeEquiv)

theorem simpleNode_involutive : Function.Involutive simpleNode := by
  intro i
  fin_cases i <;> rfl

theorem simpleNode_table (i : Fin 6) : simpleNode i = ![5, 1, 4, 3, 2, 0] i := by
  fin_cases i <;> rfl

theorem simpleNode_cartan (i j : Fin 6) :
    CartanMatrix.E 6 (simpleNode i) (simpleNode j) = CartanMatrix.E 6 i j := by
  fin_cases i <;> fin_cases j <;> rfl

noncomputable def baseDiagram : Equiv.Perm base.support :=
  baseIndexEquiv.symm.trans (simpleNode.trans baseIndexEquiv)

@[simp] theorem baseDiagram_index (i : Fin 6) :
    baseDiagram (baseIndexEquiv i) = baseIndexEquiv (simpleNode i) := by
  simp [baseDiagram]

theorem baseDiagram_involutive : Function.Involutive baseDiagram := by
  intro i
  simp only [baseDiagram, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [simpleNode_involutive (baseIndexEquiv.symm i), Equiv.apply_symm_apply]

theorem baseDiagram_root (i : base.support) :
    (baseDiagram i).val = rootDiagram i.val := by
  obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
  rw [baseDiagram_index, baseIndexEquiv_apply, baseIndexEquiv_apply, rootDiagram_simple]
  congr 1
  simp [simpleNode]

theorem baseDiagram_cartan (i j : base.support) :
    base.cartanMatrix (baseDiagram i) (baseDiagram j) = base.cartanMatrix i j := by
  obtain ⟨a, rfl⟩ := baseIndexEquiv.surjective i
  obtain ⟨b, rfl⟩ := baseIndexEquiv.surjective j
  rw [baseDiagram_index, baseDiagram_index, base_cartan, base_cartan, simpleNode_cartan]

end Atlas.Chevalley.TwistedE6
