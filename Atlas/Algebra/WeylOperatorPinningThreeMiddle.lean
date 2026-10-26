import Atlas.Algebra.WeylOperatorPinningThree
import Atlas.Algebra.FiniteHadamardTwo

/-! The middle two vectors of the length-four rational operator string.
Only the conjugating operators are nilpotent. No target group is assumed. -/

noncomputable section
namespace Atlas.Algebra
variable {S : Type*} [Ring S] [Algebra ℚ S]

theorem weyl_word_conjugate_middle_three
    (E F B C D L : S) (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEC : E * C - C * E = D) (hED : E * D - D * E = L)
    (hEL : Commute E L) (hFB : Commute F B)
    (hFC : F * C - C * F = (3 : ℚ) • B)
    (hFD : F * D - D * F = (4 : ℚ) • C)
    (hFL : F * L - L * F = (3 : ℚ) • D) :
    (IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * C *
      IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) =
        (-1 / 2 : ℚ) • D) ∧
    (IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * D *
      IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) =
        (2 : ℚ) • C) := by
  let u : S →ₗ[ℚ] S := LinearMap.mulRight ℚ (IsNilpotent.exp (-E)) ∘ₗ
    LinearMap.mulLeft ℚ (IsNilpotent.exp E)
  let v : S →ₗ[ℚ] S := LinearMap.mulRight ℚ (IsNilpotent.exp F) ∘ₗ
    LinearMap.mulLeft ℚ (IsNilpotent.exp (-F))
  have hu (x : S) : u x = IsNilpotent.exp E * x * IsNilpotent.exp (-E) := rfl
  have hv (x : S) : v x = IsNilpotent.exp (-F) * x * IsNilpotent.exp F := rfl
  have huC : u C = C + D + (1 / 2 : ℚ) • L :=
    exp_mul_mul_exp_neg_eq_add_add_half E C D L hE hEC hED hEL
  have huD : u D = D + L := by
    have h := exp_mul_mul_exp_neg_eq_add_bracket E D hE
      (by rw [hED]; exact hEL)
    rw [hu]
    simpa only [hED] using h
  have huL : u L = L := by
    have hz : E * L - L * E = 0 := sub_eq_zero.mpr hEL.eq
    have h := exp_mul_mul_exp_neg_eq_add_bracket E L hE
      (by rw [hz]; exact Commute.zero_right E)
    rw [hu]
    simpa only [hz, add_zero] using h
  have hneg (x : S) : (-F) * x - x * (-F) = -(F * x - x * F) := by
    simp only [neg_mul, mul_neg]
    abel
  have hscale (q : ℚ) (x : S) :
      (-F) * (q • x) - (q • x) * (-F) = (-q) • (F * x - x * F) := by
    simp only [mul_smul_comm, smul_mul_assoc, neg_mul, mul_neg, smul_sub,
      neg_smul, smul_neg] <;> module
  have hcomm (q : ℚ) : Commute (-F) (q • B) := by
    change (-F) * (q • B) = (q • B) * (-F)
    simp only [mul_smul_comm, smul_mul_assoc, neg_mul, mul_neg, hFB.eq, smul_neg]
  have hvC : v C = C + (-3 : ℚ) • B := by
    have hδ : (-F) * C - C * (-F) = (-3 : ℚ) • B := by
      rw [hneg, hFC]
      module
    have h := exp_mul_mul_exp_neg_eq_add_bracket (-F) C hF.neg
      (by rw [hδ]; exact hcomm (-3))
    rw [hv]
    simpa only [neg_neg, hδ] using h
  have hvD : v D = D + (-4 : ℚ) • C + (6 : ℚ) • B := by
    have hδ₁ : (-F) * D - D * (-F) = (-4 : ℚ) • C := by
      rw [hneg, hFD]
      module
    have hδ₂ : (-F) * ((-4 : ℚ) • C) - ((-4 : ℚ) • C) * (-F) =
        (12 : ℚ) • B := by
      rw [hscale, hFC]
      module
    have h := exp_mul_mul_exp_neg_eq_add_add_half
      (-F) D ((-4 : ℚ) • C) ((12 : ℚ) • B)
      hF.neg hδ₁ hδ₂ (hcomm 12)
    rw [neg_neg] at h
    calc
      _ = D + (-4 : ℚ) • C + (1 / 2 : ℚ) • ((12 : ℚ) • B) := h
      _ = _ := by module
  have hvL : v L = L + (-3 : ℚ) • D + (6 : ℚ) • C + (-6 : ℚ) • B := by
    have hδ₁ : (-F) * L - L * (-F) = (-3 : ℚ) • D := by
      rw [hneg, hFL]
      module
    have hδ₂ : (-F) * ((-3 : ℚ) • D) - ((-3 : ℚ) • D) * (-F) =
        (12 : ℚ) • C := by
      rw [hscale, hFD]
      module
    have hδ₃ : (-F) * ((12 : ℚ) • C) - ((12 : ℚ) • C) * (-F) =
        (-36 : ℚ) • B := by
      rw [hscale, hFC]
      module
    have h := exp_mul_mul_exp_neg_eq_add_add_half_add_sixth
      (-F) L ((-3 : ℚ) • D) ((12 : ℚ) • C) ((-36 : ℚ) • B)
      hF.neg hδ₁ hδ₂ hδ₃ (hcomm (-36))
    rw [neg_neg] at h
    calc
      _ = L + (-3 : ℚ) • D + (1 / 2 : ℚ) • ((12 : ℚ) • C) +
          (1 / 6 : ℚ) • ((-36 : ℚ) • B) := h
      _ = _ := by module
  have hmC : v (u C) = (-1 / 2 : ℚ) • D + (1 / 2 : ℚ) • L := by
    rw [huC]
    simp only [map_add, map_smul, hvC, hvD, hvL]
    module
  have hmD : v (u D) = (2 : ℚ) • C + (-2 : ℚ) • D + L := by
    rw [huD, map_add, hvD, hvL]
    module
  constructor
  · calc
      _ = u (v (u C)) := by simp only [hu, hv, mul_assoc]
      _ = (-1 / 2 : ℚ) • D := by
        rw [hmC]
        simp only [map_add, map_smul, huD, huL]
        module
  · calc
      _ = u (v (u D)) := by simp only [hu, hv, mul_assoc]
      _ = (2 : ℚ) • C := by
        rw [hmD]
        simp only [map_add, map_smul, huC, huD, huL]
        module

end Atlas.Algebra
