import Atlas.LinearGroups.Orthogonal.SignProductD
import Atlas.LinearGroups.Orthogonal.CenterStandard
import Atlas.LinearGroups.Orthogonal.IntrinsicStandard

/-! # Exact negative-scalar membership and center size in the actual odd split-D kernel -/
noncomputable section
open scoped Classical
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem elementaryD_center_signs (n : ℕ) (z : elementarySubgroup (formD (n+2) F)) :
    z ∈ Subgroup.center (elementarySubgroup (formD (n+2) F)) ↔
      z.val = 1 ∨ z.val = negativeScalarD (n+2) F := by
  rw [elementaryD_center_scalar]
  constructor
  · rintro ⟨c, hc, hz⟩
    rcases sq_eq_one_iff.mp hc with h | h
    · left
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change z.val.val x = x
      rw [hz, h, one_smul]
    · right
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      exact (hz x).trans (congrArg (fun c : F => c • x) h)
  · rintro (h | h)
    · exact ⟨1, one_pow 2, fun x => by rw [h]; exact (one_smul F x).symm⟩
    · exact ⟨-1, by ring, fun x => by rw [h]; rfl⟩

theorem negativeScalarD_ne_one (n : ℕ) (h2 : (2 : F) ≠ 0) :
    negativeScalarD (n+1) F ≠ 1 := by
  intro h
  have he := congrArg (fun g : isometrySubgroup (formD (n+1) F) => g.val (e 0) (.inl 0)) h
  change (-1 : F) • e (F := F) (0 : Fin (n+1)) (.inl 0) = e (F := F) (0 : Fin (n+1)) (.inl 0) at he
  simp only [e, Pi.single_eq_same, smul_eq_mul, mul_one] at he
  apply h2
  linear_combination -he

variable [Finite F]

theorem negativeScalarD_mem_elementary_iff (n : ℕ) (h2 : (2 : F) ≠ 0) :
    negativeScalarD (n+2) F ∈ elementarySubgroup (formD (n+2) F) ↔
      ∃ b : Fˣ, b^2 = (-1 : Fˣ)^(n+2) := by
  rw [elementaryD_eq_intrinsicKernel n h2]
  change (determinant (formD (n+2) F) (negativeScalarD (n+2) F) = 1 ∧
    spinorNorm (formD (n+2) F) polarD_nondegenerate h2 (negativeScalarD (n+2) F) = 1) ↔ _
  rw [negativeScalarD_determinant, negativeScalarD_spinorNorm, eq_self, true_and, Atlas.squareClass_eq_one]

theorem card_elementaryD_center (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.center (elementarySubgroup (formD (n+2) F))) =
      if ∃ b : Fˣ, b^2 = (-1 : Fˣ)^(n+2) then 2 else 1 := by
  classical
  by_cases h : ∃ b : Fˣ, b^2 = (-1 : Fˣ)^(n+2)
  · rw [if_pos h]
    have hm := (negativeScalarD_mem_elementary_iff n h2).mpr h
    let z : elementarySubgroup (formD (n+2) F) := ⟨negativeScalarD (n+2) F, hm⟩
    have hz : z ∈ Subgroup.center (elementarySubgroup (formD (n+2) F)) :=
      (elementaryD_center_signs n z).mpr (Or.inr rfl)
    apply Nat.card_eq_two_iff.mpr
    refine ⟨1, ⟨z, hz⟩, ?_, ?_⟩
    · intro he
      have hv := congrArg (fun t : Subgroup.center (elementarySubgroup (formD (n+2) F)) => t.val.val) he
      exact negativeScalarD_ne_one (n+1) h2 hv.symm
    · apply Set.eq_univ_of_forall
      intro t
      rcases (elementaryD_center_signs n t.val).mp t.prop with ht | ht
      · have he : t = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          exact ht
        simp [he]
      · have he : t = ⟨z, hz⟩ := by
          apply Subtype.ext
          apply Subtype.ext
          exact ht
        simp [he]
  · rw [if_neg h]
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, ?_⟩
    intro z
    rcases (elementaryD_center_signs n z.val).mp z.prop with hz | hz
    · apply Subtype.ext
      apply Subtype.ext
      exact hz
    · exact (h ((negativeScalarD_mem_elementary_iff n h2).mp (hz ▸ z.val.prop))).elim
end Atlas.Orthogonal
