import Atlas.LinearGroups.Orthogonal.Minus.OddScalarSpinor
import Atlas.LinearGroups.Orthogonal.Minus.IntrinsicOdd
import Atlas.LinearGroups.Orthogonal.Center
import Atlas.LinearGroups.Orthogonal.Minus.CenterArithmetic

/-! Exact negative-scalar membership and odd-characteristic center cardinality. -/
noncomputable section
open scoped Classical
namespace Atlas

theorem twice_minus_center_factor (q n : ℕ) (hq : q % 2 = 1) :
    2 * (if q^n % 4 = 3 then 2 else 1) = Nat.gcd 4 (q^n+1) := by
  have hp : q^n % 2 = 1 := by simp [Nat.pow_mod, hq]
  have hmod := Nat.mod_lt (q^n) (by decide : 0 < 4)
  by_cases h : q^n % 4 = 3
  · have hx : (q^n+1) % 4 = 0 := by omega
    rw [ite_eq_left h, Nat.gcd_rec, hx]
    norm_num
  · have hx : (q^n+1) % 4 = 2 := by omega
    rw [ite_eq_right h, Nat.gcd_rec, hx]
    norm_num
end Atlas

namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem elementary_center_signs (hdeg : Module.finrank F K = 2) (n : ℕ)
    (z : E hdeg (n+2)) :
    z ∈ Subgroup.center (E hdeg (n+2)) ↔
      z.val = 1 ∨ z.val = negativeScalar hdeg (n+2) := by
  rw [mem_elementary_center_iff_scalar _ (wittTwoFrame hdeg n)
    (polar_nondegenerate hdeg (n+2))]
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

theorem negativeScalar_ne_one (hdeg : Module.finrank F K = 2) (k : ℕ)
    (h2 : (2 : F) ≠ 0) : negativeScalar hdeg k ≠ 1 := by
  intro h
  have he := congrArg (fun g : O hdeg k => (g.val (0,1)).2) h
  change (-1 : F) • (1 : K) = 1 at he
  have hm : algebraMap F K (-1) = algebraMap F K 1 := by
    simpa only [Algebra.smul_def, mul_one, map_one] using he
  have hs := (algebraMap F K).injective hm
  apply h2
  linear_combination -hs

theorem negativeScalar_spinorNorm_eq_one_iff_mod_four
    (hdeg : Module.finrank F K = 2) (k : ℕ) (h2 : (2 : F) ≠ 0) :
    spinorNorm (form hdeg k) (polar_nondegenerate hdeg k) h2
      (negativeScalar hdeg k) = 1 ↔ Nat.card F^(k+1)%4=3 := by
  obtain ⟨t, ht, htrace⟩ := Atlas.FiniteQuadratic.exists_nonzero_trace_zero hdeg
  let u : Fˣ := Units.mk0 (Algebra.norm F t)
    (fun h => ht ((Atlas.FiniteQuadratic.norm_zero_iff hdeg t).mp h))
  have hd : ¬ IsSquare ((-u).val) :=
    trace_zero_discriminant_nonsquare hdeg h2 t ht htrace
  have he : (-1 : Fˣ)^k * u = (-1 : Fˣ)^(k+1) * (-u) := by
    rw [pow_succ]
    simp only [mul_neg, neg_mul, neg_neg, mul_one]
  rw [negativeScalar_spinorNorm hdeg k h2 t ht htrace]
  change Atlas.squareClass F ((-1 : Fˣ)^k * u) = 1 ↔ _
  rw [he, Atlas.squareClass_mul_nonsquare_eq_one_iff h2 _ _ hd,
    Atlas.sign_power_square_iff_card_pow_mod_four h2]
  have hp : Nat.card F^(k+1)%2=1 := by
    simp [Nat.pow_mod, Atlas.odd_card_mod_two h2]
  have hm := Nat.mod_lt (Nat.card F^(k+1)) (by decide : 0<4)
  omega

theorem negativeScalar_mem_elementary_iff_mod_four
    (hdeg : Module.finrank F K = 2) (n : ℕ) (h2 : (2 : F) ≠ 0) :
    negativeScalar hdeg (n+2) ∈ E hdeg (n+2) ↔ Nat.card F^(n+3)%4=3 := by
  rw [elementary_eq_intrinsic_kernel hdeg n h2]
  change (determinant (form hdeg (n+2)) (negativeScalar hdeg (n+2)) = 1 ∧
    spinorNorm (form hdeg (n+2)) (polar_nondegenerate hdeg _) h2
      (negativeScalar hdeg (n+2)) = 1) ↔ _
  rw [negativeScalar_determinant hdeg (n+2) h2, eq_self, true_and]
  exact negativeScalar_spinorNorm_eq_one_iff_mod_four hdeg (n+2) h2

theorem card_elementary_center_mod_four
    (hdeg : Module.finrank F K = 2) (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.center (E hdeg (n+2))) =
      if Nat.card F^(n+3)%4=3 then 2 else 1 := by
  classical
  by_cases h : Nat.card F^(n+3)%4=3
  · rw [ite_eq_left h]
    have hm := (negativeScalar_mem_elementary_iff_mod_four hdeg n h2).mpr h
    let z : E hdeg (n+2) := ⟨negativeScalar hdeg (n+2), hm⟩
    have hz : z ∈ Subgroup.center (E hdeg (n+2)) :=
      (elementary_center_signs hdeg n z).mpr (Or.inr rfl)
    apply Nat.card_eq_two_iff.mpr
    refine ⟨1, ⟨z, hz⟩, ?_, ?_⟩
    · intro he
      have hv := congrArg (fun t : Subgroup.center (E hdeg (n+2)) => t.val.val) he
      exact negativeScalar_ne_one hdeg (n+2) h2 hv.symm
    · apply Set.eq_univ_of_forall
      intro t
      rcases (elementary_center_signs hdeg n t.val).mp t.prop with ht | ht
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
  · rw [ite_eq_right h]
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨1, ?_⟩
    intro z
    rcases (elementary_center_signs hdeg n z.val).mp z.prop with hz | hz
    · apply Subtype.ext
      apply Subtype.ext
      exact hz
    · exact (h ((negativeScalar_mem_elementary_iff_mod_four hdeg n h2).mp
        (hz ▸ z.val.prop))).elim

theorem card_elementary_center_mul_two
    (hdeg : Module.finrank F K = 2) (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.center (E hdeg (n+2))) * 2 = Nat.gcd 4 (Nat.card F^(n+3)+1) := by
  rw [card_elementary_center_mod_four hdeg n h2, mul_comm]
  exact Atlas.twice_minus_center_factor _ _ (Atlas.odd_card_mod_two h2)
end Atlas.Orthogonal.Minus
