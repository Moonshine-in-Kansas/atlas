import Atlas.LinearGroups.Chevalley.RootData.E6
import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesD
import Mathlib.LinearAlgebra.Basis.Basic

/-! The actual D5 root lattice embeds in the node-zero-omitted E6 span.
Root images are certified by simple-reflection induction. This is an integral
root embedding, not yet a homomorphism of the full actual Weyl groups. -/
noncomputable section
namespace Atlas.Chevalley.E6D5
open Classical
private abbrev DP := ClassicalData.pairingD 5
private abbrev db := ClassicalData.baseD 3
private abbrev Q := E6Data.pairing
private abbrev qb := E6Data.base

/-- The pinned D5 chain and fork map to the five E6 nodes other than zero. -/
def nodeEmbedding : Fin 5 ↪ Fin 6 where
  toFun := ![5, 4, 3, 2, 1]
  inj' := by decide

/-- Embedding of actual simple-root indices, using both pinned base equivalences. -/
def simpleEmbedding : db.support ↪ qb.support where
  toFun i := E6Data.baseIndexEquiv
    (nodeEmbedding ((ClassicalData.baseDIndexEquiv 3).symm i))
  inj' := by
    intro i j h
    apply (ClassicalData.baseDIndexEquiv 3).symm.injective
    exact nodeEmbedding.injective (E6Data.baseIndexEquiv.injective h)

theorem simpleEmbedding_cartan (i j : db.support) :
    qb.cartanMatrix (simpleEmbedding i) (simpleEmbedding j) =
      db.cartanMatrix i j := by
  obtain ⟨a, rfl⟩ := (ClassicalData.baseDIndexEquiv 3).surjective i
  obtain ⟨b, rfl⟩ := (ClassicalData.baseDIndexEquiv 3).surjective j
  change E6Data.base.cartanMatrix
      (E6Data.baseIndexEquiv (nodeEmbedding
        ((ClassicalData.baseDIndexEquiv 3).symm ((ClassicalData.baseDIndexEquiv 3) a))))
      (E6Data.baseIndexEquiv (nodeEmbedding
        ((ClassicalData.baseDIndexEquiv 3).symm ((ClassicalData.baseDIndexEquiv 3) b)))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    E6Data.base_cartan, ClassicalData.baseD_cartan]
  fin_cases a <;> fin_cases b <;>
    norm_num [CartanMatrix.E, CartanMatrix.D, nodeEmbedding] <;> decide

/-- Integral root-span map on the genuine D5 simple-root basis. No division by
2 or by a Cartan determinant is used to define this map. -/
def latticeEmbedding : DP.rootSpan ℤ →ₗ[ℤ] E6Data.Lattice :=
  db.toWeightBasisInt.constr ℤ (fun i => Q.root (simpleEmbedding i).val)

theorem latticeEmbedding_simple (i : db.support) :
    latticeEmbedding (DP.rootSpanMem ℤ i.val) = Q.root (simpleEmbedding i).val := by
  have hi : DP.rootSpanMem ℤ i.val = db.toWeightBasisInt i := by
    apply Subtype.ext
    exact (db.coe_toWeightBasisInt_apply i).symm
  rw [hi]
  simp only [latticeEmbedding, Module.Basis.constr_basis]

theorem latticeEmbedding_injective : Function.Injective latticeEmbedding := by
  have hi : LinearIndependent ℤ (fun k : qb.support => Q.root k.val) :=
    qb.linearIndepOn_root
  exact db.toWeightBasisInt.injective_constr_of_linearIndependent
    (hi.comp simpleEmbedding simpleEmbedding.injective)

/-- Pairing with every embedded simple root agrees on the whole integral D5
root lattice, not only on the simple-root columns. -/
theorem latticeEmbedding_pairing (i : db.support) (x : DP.rootSpan ℤ) :
    E6Data.polar (Q.root (simpleEmbedding i).val) (latticeEmbedding x) =
      DP.coroot i.val x.val := by
  have h : (E6Data.polar (Q.root (simpleEmbedding i).val)).comp latticeEmbedding =
      (DP.coroot i.val).comp (DP.rootSpan ℤ).subtype := by
    apply db.toWeightBasisInt.ext
    intro j
    have hj : db.toWeightBasisInt j = DP.rootSpanMem ℤ j.val := by
      apply Subtype.ext
      exact db.coe_toWeightBasisInt_apply j
    simp only [hj, LinearMap.comp_apply]
    rw [latticeEmbedding_simple]
    have hQ := Q.algebraMap_pairingIn ℤ (simpleEmbedding j).val (simpleEmbedding i).val
    change qb.cartanMatrix (simpleEmbedding j) (simpleEmbedding i) =
      E6Data.polar (Q.root (simpleEmbedding i).val) (Q.root (simpleEmbedding j).val) at hQ
    have hD := DP.algebraMap_pairingIn ℤ j.val i.val
    change db.cartanMatrix j i = DP.coroot i.val (DP.root j.val) at hD
    rw [← hQ, simpleEmbedding_cartan, hD]
    rfl
  exact congrArg (fun f : DP.rootSpan ℤ →ₗ[ℤ] ℤ => f x) h

theorem latticeEmbedding_reflection_simple (i : db.support)
    (β : ClassicalData.DRoot 5) :
    latticeEmbedding (DP.rootSpanMem ℤ (DP.reflectionPerm i.val β)) =
      E6Data.reflect (simpleEmbedding i).val
        (latticeEmbedding (DP.rootSpanMem ℤ β)) := by
  have hs : DP.rootSpanMem ℤ (DP.reflectionPerm i.val β) =
      DP.rootSpanMem ℤ β - DP.pairing β i.val • DP.rootSpanMem ℤ i.val := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_smul,
      DP.root_reflectionPerm, DP.reflection_apply_root]
  rw [hs, map_sub, map_smul, latticeEmbedding_simple]
  change latticeEmbedding (DP.rootSpanMem ℤ β) -
      DP.coroot i.val (DP.root β) • Q.root (simpleEmbedding i).val =
    latticeEmbedding (DP.rootSpanMem ℤ β) -
      E6Data.polar (Q.root (simpleEmbedding i).val)
        (latticeEmbedding (DP.rootSpanMem ℤ β)) • Q.root (simpleEmbedding i).val
  rw [latticeEmbedding_pairing]

/-- Every actual D5 root maps to an actual integral E6 root. -/
theorem latticeEmbedding_root_mem (β : ClassicalData.DRoot 5) :
    latticeEmbedding (DP.rootSpanMem ℤ β) ∈ Set.range Q.root := by
  apply db.induction_reflect β
  · intro γ hγ
    obtain ⟨δ, hδ⟩ := hγ
    refine ⟨Q.reflectionPerm δ δ, ?_⟩
    rw [DP.rootSpanMem_reflectionPerm_self, map_neg, ← hδ]
    simp
  · intro γ hγ
    exact ⟨(simpleEmbedding ⟨γ, hγ⟩).val,
      (latticeEmbedding_simple ⟨γ, hγ⟩).symm⟩
  · intro γ i hγ hi
    obtain ⟨δ, hδ⟩ := hγ
    refine ⟨Q.reflectionPerm (simpleEmbedding ⟨i, hi⟩).val δ, ?_⟩
    rw [latticeEmbedding_reflection_simple ⟨i, hi⟩ γ, ← hδ]
    rfl

/-- Actual root-label embedding extracted from the integral root map. -/
def rootEmbedding : ClassicalData.DRoot 5 ↪ E6Data.Root where
  toFun β := Classical.choose (latticeEmbedding_root_mem β)
  inj' := by
    intro β γ h
    have hβ := Classical.choose_spec (latticeEmbedding_root_mem β)
    have hγ := Classical.choose_spec (latticeEmbedding_root_mem γ)
    have he := hβ.symm.trans ((congrArg Q.root h).trans hγ)
    have hroot : DP.root β = DP.root γ :=
      congrArg (fun x : DP.rootSpan ℤ => x.val) (latticeEmbedding_injective he)
    exact DP.root.injective hroot

theorem rootEmbedding_root (β : ClassicalData.DRoot 5) :
    Q.root (rootEmbedding β) = latticeEmbedding (DP.rootSpanMem ℤ β) :=
  Classical.choose_spec (latticeEmbedding_root_mem β)

theorem rootEmbedding_simple (i : db.support) :
    rootEmbedding i.val = (simpleEmbedding i).val := by
  apply Q.root.injective
  rw [rootEmbedding_root, latticeEmbedding_simple]

theorem rootEmbedding_reflection_simple (i : db.support)
    (β : ClassicalData.DRoot 5) :
    rootEmbedding (DP.reflectionPerm i.val β) =
      Q.reflectionPerm (simpleEmbedding i).val (rootEmbedding β) := by
  apply Q.root.injective
  rw [rootEmbedding_root, latticeEmbedding_reflection_simple]
  change E6Data.reflect (simpleEmbedding i).val
      (latticeEmbedding (DP.rootSpanMem ℤ β)) =
    E6Data.reflect (simpleEmbedding i).val (Q.root (rootEmbedding β))
  rw [rootEmbedding_root]

end Atlas.Chevalley.E6D5
