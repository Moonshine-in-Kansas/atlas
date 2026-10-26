import Atlas.Algebra.WeylOperatorPinningTwo

/-! The middle of a length-three operator string has Weyl sign minus. -/
noncomputable section
namespace Atlas.Algebra
variable {S : Type*} [Ring S] [Algebra ℚ S]

theorem weyl_word_conjugate_middle_eq_neg
    (E F B C D : S) (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEC : E * C - C * E = D) (hED : Commute E D) (hFB : Commute F B)
    (hFC : F * C - C * F = (2 : ℚ) • B)
    (hFD : F * D - D * F = (2 : ℚ) • C) :
    IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * C *
      IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) = -C := by
  have hfirst : IsNilpotent.exp E * C * IsNilpotent.exp (-E) = C + D := by
    have hcomm : Commute E (E * C - C * E) := by
      rw [hEC]
      exact hED
    simpa only [hEC] using exp_mul_mul_exp_neg_eq_add_bracket E C hE hcomm
  have hFBzero : F * B - B * F = 0 := sub_eq_zero.mpr hFB.eq
  have hmiddleBracket : (-F) * (C + D) - (C + D) * (-F) =
      (-2 : ℚ) • B + (-2 : ℚ) • C := by
    calc
      (-F) * (C + D) - (C + D) * (-F) =
          -(F * C - C * F) - (F * D - D * F) := by
        simp only [neg_mul, mul_neg, mul_add, add_mul]
        module
      _ = (-2 : ℚ) • B + (-2 : ℚ) • C := by rw [hFC, hFD]; module
  have hmiddleSecond :
      (-F) * ((-2 : ℚ) • B + (-2 : ℚ) • C) -
        ((-2 : ℚ) • B + (-2 : ℚ) • C) * (-F) = (4 : ℚ) • B := by
    calc
      (-F) * ((-2 : ℚ) • B + (-2 : ℚ) • C) -
          ((-2 : ℚ) • B + (-2 : ℚ) • C) * (-F) =
          (2 : ℚ) • (F * B - B * F) + (2 : ℚ) • (F * C - C * F) := by
        simp only [neg_mul, mul_neg, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, smul_sub]
        module
      _ = (4 : ℚ) • B := by rw [hFBzero, hFC]; module
  have hmiddleComm : Commute (-F) ((4 : ℚ) • B) :=
    hFB.neg_left.smul_right (4 : ℚ)
  have hmiddle : IsNilpotent.exp (-F) * (C + D) * IsNilpotent.exp F = D - C := by
    have h := exp_mul_mul_exp_neg_eq_add_add_half (-F) (C + D)
      ((-2 : ℚ) • B + (-2 : ℚ) • C) ((4 : ℚ) • B)
      hF.neg hmiddleBracket hmiddleSecond hmiddleComm
    rw [neg_neg] at h
    calc
      _ = (C + D) + ((-2 : ℚ) • B + (-2 : ℚ) • C) +
          (1 / 2 : ℚ) • ((4 : ℚ) • B) := h
      _ = D - C := by module
  have hlastBracket : E * (D - C) - (D - C) * E = -D := by
    calc
      E * (D - C) - (D - C) * E =
          (E * D - D * E) - (E * C - C * E) := by
        simp only [mul_sub, sub_mul]
        module
      _ = -D := by rw [sub_eq_zero.mpr hED.eq, hEC, zero_sub]
  have hlast : IsNilpotent.exp E * (D - C) * IsNilpotent.exp (-E) = -C := by
    have hcomm : Commute E (E * (D - C) - (D - C) * E) := by
      rw [hlastBracket]
      exact hED.neg_right
    have h := exp_mul_mul_exp_neg_eq_add_bracket E (D - C) hE hcomm
    rw [hlastBracket] at h
    calc
      _ = D - C + -D := h
      _ = -C := by abel
  calc
    _ = IsNilpotent.exp E *
        (IsNilpotent.exp (-F) *
          (IsNilpotent.exp E * C * IsNilpotent.exp (-E)) * IsNilpotent.exp F) *
        IsNilpotent.exp (-E) := by simp only [mul_assoc]
    _ = -C := by rw [hfirst, hmiddle, hlast]

end Atlas.Algebra
