import Atlas.LinearGroups.Unitary.Reindex

/-! Repeated identity-coordinate extension with exact support behavior. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

def padSpecialHom (hdeg : Module.finrank F K = 2) :
    (k : ℕ) → (SU F K n hdeg →* SU F K (n+k) hdeg)
  | 0 => MonoidHom.id _
  | k+1 => (extendSpecialHom hdeg).comp (padSpecialHom hdeg k)

def padIndex (n : ℕ) : (k : ℕ) → (Fin n ↪ Fin (n+k))
  | 0 => Function.Embedding.refl _
  | k+1 => (padIndex n k).trans ⟨Fin.succ, Fin.succ_injective _⟩

@[simp] theorem padIndex_zero (i : Fin n) : padIndex n 0 i = i := rfl
@[simp] theorem padIndex_succ (k : ℕ) (i : Fin n) :
    padIndex n (k+1) i = (padIndex n k i).succ := rfl

theorem padSpecialHom_generated (hdeg : Module.finrank F K = 2) (k : ℕ)
    (g : SU F K n hdeg) (hg : g ∈ transvectionGenerated hdeg) :
    padSpecialHom hdeg k g ∈ transvectionGenerated hdeg := by
  induction k with
  | zero => exact hg
  | succ k ih => exact extendSpecialHom_generated hdeg _ ih

/-- The selected block carries exactly the original matrix action. -/
theorem padSpecialHom_apply_inside (hdeg : Module.finrank F K = 2) (k : ℕ)
    (g : SU F K n hdeg) (v : Fin (n+k) → K) (i : Fin n) :
    ((padSpecialHom hdeg k g).val *ᵥ v) (padIndex n k i) =
      (g.val *ᵥ (v ∘ padIndex n k)) i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (extendMatrix (padSpecialHom hdeg k g).val *ᵥ v) (padIndex n k i).succ = _
    rw [extendMatrix_mulVec]
    simpa only [Fin.cons_succ, Function.comp_def, padIndex_succ, Fin.tail] using ih (Fin.tail v)

/-- Every coordinate outside the block is fixed pointwise. -/
theorem padSpecialHom_apply_outside (hdeg : Module.finrank F K = 2) (k : ℕ)
    (g : SU F K n hdeg) (v : Fin (n+k) → K) (i : Fin (n+k))
    (hi : i ∉ Set.range (padIndex n k)) : ((padSpecialHom hdeg k g).val *ᵥ v) i = v i := by
  induction k with
  | zero => exact (hi ⟨i,rfl⟩).elim
  | succ k ih =>
    change (extendMatrix (padSpecialHom hdeg k g).val *ᵥ v) i = _
    rw [extendMatrix_mulVec]
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi; rfl
    · intro hi
      change ((padSpecialHom hdeg k g).val *ᵥ Fin.tail v) j = v j.succ
      apply ih (Fin.tail v) j
      rintro ⟨x,hx⟩
      apply hi
      exact ⟨x, congrArg Fin.succ hx⟩
end Atlas.Unitary
