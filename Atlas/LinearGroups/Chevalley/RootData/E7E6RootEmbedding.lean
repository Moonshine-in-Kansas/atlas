import Atlas.LinearGroups.Chevalley.RootData.E6
import Atlas.LinearGroups.Chevalley.RootData.E7
import Mathlib.LinearAlgebra.Basis.Basic

/-! The actual integral E6 roots embed in the first-six-node subsystem of E7.
The construction uses the simple-root bases, their actual Cartan entries and
reflection induction. It uses no group order or orthogonal complement. -/
noncomputable section
set_option maxRecDepth 32768
namespace Atlas.Chevalley.E7E6
open Classical
private abbrev P := E6Data.pairing
private abbrev b := E6Data.base
private abbrev Q := E7Data.pairing
private abbrev c := E7Data.base

/-- The first six pinned E7 nodes are the pinned E6 diagram. -/
def nodeEmbedding : Fin 6 ↪ Fin 7 where
  toFun i := i.castSucc
  inj' := Fin.castSucc_injective 6

/-- The actual simple-root embedding, including the E6 coordinate renumbering. -/
def simpleEmbedding : b.support ↪ c.support where
  toFun i := E7Data.baseIndexEquiv (nodeEmbedding (E6Data.baseIndexEquiv.symm i))
  inj' := by
    intro i j h
    apply E6Data.baseIndexEquiv.symm.injective
    exact nodeEmbedding.injective (E7Data.baseIndexEquiv.injective h)

theorem simpleEmbedding_cartan (i j : b.support) :
    c.cartanMatrix (simpleEmbedding i) (simpleEmbedding j) = b.cartanMatrix i j := by
  obtain ⟨a, rfl⟩ := E6Data.baseIndexEquiv.surjective i
  obtain ⟨d, rfl⟩ := E6Data.baseIndexEquiv.surjective j
  change E7Data.base.cartanMatrix
      (E7Data.baseIndexEquiv (nodeEmbedding
        (E6Data.baseIndexEquiv.symm (E6Data.baseIndexEquiv a))))
      (E7Data.baseIndexEquiv (nodeEmbedding
        (E6Data.baseIndexEquiv.symm (E6Data.baseIndexEquiv d)))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    E7Data.base_cartan, E6Data.base_cartan]
  fin_cases a <;> fin_cases d <;> norm_num [CartanMatrix.E, nodeEmbedding] <;> decide

/-- Integral extension from the actual E6 simple-root basis. -/
def latticeEmbedding : P.rootSpan ℤ →ₗ[ℤ] E7Data.Lattice :=
  b.toWeightBasisInt.constr ℤ (fun i => Q.root (simpleEmbedding i).val)

theorem latticeEmbedding_simple (i : b.support) :
    latticeEmbedding (P.rootSpanMem ℤ i.val) = Q.root (simpleEmbedding i).val := by
  have hi : P.rootSpanMem ℤ i.val = b.toWeightBasisInt i := by
    apply Subtype.ext
    exact (b.coe_toWeightBasisInt_apply i).symm
  rw [hi]
  simp only [latticeEmbedding, Module.Basis.constr_basis]

theorem latticeEmbedding_injective : Function.Injective latticeEmbedding := by
  have hi : LinearIndependent ℤ (fun k : c.support => Q.root k.val) :=
    c.linearIndepOn_root
  exact b.toWeightBasisInt.injective_constr_of_linearIndependent
    (hi.comp simpleEmbedding simpleEmbedding.injective)

/-- Pairing with each embedded simple coroot agrees on the entire E6 root span. -/
theorem latticeEmbedding_pairing (i : b.support) (x : P.rootSpan ℤ) :
    Q.coroot' (simpleEmbedding i).val (latticeEmbedding x) = P.coroot' i.val x.val := by
  have h : (Q.coroot' (simpleEmbedding i).val).comp latticeEmbedding =
      (P.coroot' i.val).comp (P.rootSpan ℤ).subtype := by
    apply b.toWeightBasisInt.ext
    intro j
    have hj : b.toWeightBasisInt j = P.rootSpanMem ℤ j.val := by
      apply Subtype.ext
      exact b.coe_toWeightBasisInt_apply j
    simp only [hj, LinearMap.comp_apply]
    rw [latticeEmbedding_simple]
    have hQ := Q.algebraMap_pairingIn ℤ (simpleEmbedding j).val (simpleEmbedding i).val
    change c.cartanMatrix (simpleEmbedding j) (simpleEmbedding i) =
      Q.coroot' (simpleEmbedding i).val (Q.root (simpleEmbedding j).val) at hQ
    have hP := P.algebraMap_pairingIn ℤ j.val i.val
    change b.cartanMatrix j i = P.coroot' i.val (P.root j.val) at hP
    rw [← hQ, simpleEmbedding_cartan, hP]
    rfl
  exact congrArg (fun f : P.rootSpan ℤ →ₗ[ℤ] ℤ => f x) h

theorem latticeEmbedding_reflection_simple (i : b.support) (β : E6Data.Root) :
    latticeEmbedding (P.rootSpanMem ℤ (P.reflectionPerm i.val β)) =
      Q.reflection (simpleEmbedding i).val (latticeEmbedding (P.rootSpanMem ℤ β)) := by
  have hs : P.rootSpanMem ℤ (P.reflectionPerm i.val β) =
      P.rootSpanMem ℤ β - P.pairing β i.val • P.rootSpanMem ℤ i.val := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_smul,
      P.root_reflectionPerm, P.reflection_apply_root]
  rw [hs, map_sub, map_smul, latticeEmbedding_simple, Q.reflection_apply]
  rw [latticeEmbedding_pairing]
  rfl

/-- Every actual E6 root maps to an actual E7 root. -/
theorem latticeEmbedding_root_mem (β : E6Data.Root) :
    latticeEmbedding (P.rootSpanMem ℤ β) ∈ Set.range Q.root := by
  apply b.induction_reflect β
  · intro γ hγ
    obtain ⟨δ, hδ⟩ := hγ
    refine ⟨Q.reflectionPerm δ δ, ?_⟩
    rw [P.rootSpanMem_reflectionPerm_self, map_neg, ← hδ]
    simp
  · intro γ hγ
    exact ⟨(simpleEmbedding ⟨γ, hγ⟩).val,
      (latticeEmbedding_simple ⟨γ, hγ⟩).symm⟩
  · intro γ i hγ hi
    obtain ⟨δ, hδ⟩ := hγ
    refine ⟨Q.reflectionPerm (simpleEmbedding ⟨i, hi⟩).val δ, ?_⟩
    rw [latticeEmbedding_reflection_simple ⟨i, hi⟩ γ, ← hδ]
    exact Q.root_reflectionPerm _ _

/-- The actual root-label embedding, extracted from the integral root map. -/
def rootEmbedding : E6Data.Root ↪ E7Data.Root where
  toFun β := Classical.choose (latticeEmbedding_root_mem β)
  inj' := by
    intro β γ h
    have hβ := Classical.choose_spec (latticeEmbedding_root_mem β)
    have hγ := Classical.choose_spec (latticeEmbedding_root_mem γ)
    have he := hβ.symm.trans ((congrArg Q.root h).trans hγ)
    have hroot : P.root β = P.root γ :=
      congrArg (fun x : P.rootSpan ℤ => x.val) (latticeEmbedding_injective he)
    exact P.root.injective hroot

theorem rootEmbedding_root (β : E6Data.Root) :
    Q.root (rootEmbedding β) = latticeEmbedding (P.rootSpanMem ℤ β) :=
  Classical.choose_spec (latticeEmbedding_root_mem β)

theorem rootEmbedding_simple (i : b.support) :
    rootEmbedding i.val = (simpleEmbedding i).val := by
  apply Q.root.injective
  rw [rootEmbedding_root, latticeEmbedding_simple]

theorem rootEmbedding_reflection_simple (i : b.support) (β : E6Data.Root) :
    rootEmbedding (P.reflectionPerm i.val β) =
      Q.reflectionPerm (simpleEmbedding i).val (rootEmbedding β) := by
  apply Q.root.injective
  rw [rootEmbedding_root, latticeEmbedding_reflection_simple, Q.root_reflectionPerm,
    rootEmbedding_root]

end Atlas.Chevalley.E7E6
