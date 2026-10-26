import Atlas.LinearGroups.Unitary.Padding
import Mathlib.Logic.Equiv.Fintype

/-! Actual special-unitary blocks on arbitrary selected coordinate sets. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n k : ℕ}

/-- Extend the selected coordinate bijection to a permutation of all coordinates. -/
def blockPermutation (I : Fin n ↪ Fin (n+k)) : Equiv.Perm (Fin (n+k)) :=
  ((padIndex n k).toEquivRange.symm.trans I.toEquivRange).extendSubtype

@[simp] theorem blockPermutation_apply (I : Fin n ↪ Fin (n+k)) (i : Fin n) :
    blockPermutation I (padIndex n k i) = I i := by
  rw [blockPermutation, Equiv.extendSubtype_apply_of_mem _ _ (Set.mem_range_self i)]
  simp

private theorem reindexSpecialHom_mulVec (hdeg : Module.finrank F K = 2)
    (e : Equiv.Perm (Fin n)) (g : SU F K n hdeg) (v : Fin n → K) (i : Fin n) :
    ((reindexSpecialHom hdeg e g).val *ᵥ v) i = (g.val *ᵥ (v ∘ e)) (e.symm i) := by
  change (∑ j, g.val (e.symm i) (e.symm j) * v j) = ∑ j, g.val (e.symm i) j * v (e j)
  simpa using (Equiv.sum_comp e (fun j => g.val (e.symm i) (e.symm j) * v j)).symm

/-- Embed on the selected coordinates and fix every other coordinate. -/
def coordinateBlockHom (hdeg : Module.finrank F K = 2) (I : Fin n ↪ Fin (n+k)) :
    SU F K n hdeg →* SU F K (n+k) hdeg :=
  (reindexSpecialHom hdeg (blockPermutation I)).comp (padSpecialHom hdeg k)

theorem coordinateBlockHom_generated (hdeg : Module.finrank F K = 2)
    (I : Fin n ↪ Fin (n+k)) (g : SU F K n hdeg) (hg : g ∈ transvectionGenerated hdeg) :
    coordinateBlockHom hdeg I g ∈ transvectionGenerated hdeg :=
  reindexSpecialHom_generated hdeg _ _ (padSpecialHom_generated hdeg k g hg)

/-- Exact action on every selected coordinate. -/
theorem coordinateBlockHom_apply_inside (hdeg : Module.finrank F K = 2)
    (I : Fin n ↪ Fin (n+k)) (g : SU F K n hdeg) (v : Fin (n+k) → K) (i : Fin n) :
    ((coordinateBlockHom hdeg I g).val *ᵥ v) (I i) = (g.val *ᵥ (v ∘ I)) i := by
  change ((reindexSpecialHom hdeg (blockPermutation I) (padSpecialHom hdeg k g)).val *ᵥ v) (I i) = _
  rw [reindexSpecialHom_mulVec, ← blockPermutation_apply I i, Equiv.symm_apply_apply,
    padSpecialHom_apply_inside]
  congr 1
  funext j
  exact congrArg v (blockPermutation_apply I j)

/-- Exact pointwise fixation of every coordinate outside the selected block. -/
theorem coordinateBlockHom_apply_outside (hdeg : Module.finrank F K = 2)
    (I : Fin n ↪ Fin (n+k)) (g : SU F K n hdeg) (v : Fin (n+k) → K) (i : Fin (n+k))
    (hi : i ∉ Set.range I) : ((coordinateBlockHom hdeg I g).val *ᵥ v) i = v i := by
  change ((reindexSpecialHom hdeg (blockPermutation I) (padSpecialHom hdeg k g)).val *ᵥ v) i = _
  rw [reindexSpecialHom_mulVec]
  have hout : (blockPermutation I).symm i ∉ Set.range (padIndex n k) := by
    rintro ⟨j,hj⟩
    apply hi
    refine ⟨j, ?_⟩
    have h := congrArg (blockPermutation I) hj
    simpa using h
  rw [padSpecialHom_apply_outside hdeg k g _ _ hout]
  simp
end Atlas.Unitary
