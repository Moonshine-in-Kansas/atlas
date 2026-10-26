import Atlas.Algebra.FiniteHadamard

/-! Pinning a length-two operator string by the three-exponential Weyl word.
Only its two conjugating operators need to be nilpotent. -/

noncomputable section
namespace Atlas.Algebra

variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- If E and F act on B,C as the two elementary operators of a length-two
string, the Weyl word exp(E)exp(-F)exp(E) sends B to C by conjugation. -/
theorem weyl_word_conjugate_operator_eq
    (E F B C : S) (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEB : E * B - B * E = C) (hEC : Commute E C)
    (hFB : Commute F B) (hFC : F * C - C * F = B) :
    IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * B *
      IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) = C := by
  have hfirstComm : Commute E (E * B - B * E) := by
    simpa only [hEB] using hEC
  have hfirst : IsNilpotent.exp E * B * IsNilpotent.exp (-E) = B + C := by
    simpa only [hEB] using
      exp_mul_mul_exp_neg_eq_add_bracket E B hE hfirstComm
  have hFBzero : F * B - B * F = 0 := sub_eq_zero.mpr hFB.eq
  have hmiddleBracket : (-F) * (B + C) - (B + C) * (-F) = -B := by
    calc
      (-F) * (B + C) - (B + C) * (-F) =
          -(F * B - B * F) - (F * C - C * F) := by
        simp only [neg_mul, mul_neg, mul_add, add_mul]
        abel
      _ = -B := by rw [hFBzero, hFC, neg_zero, zero_sub]
  have hmiddleComm : Commute (-F) ((-F) * (B + C) - (B + C) * (-F)) := by
    rw [hmiddleBracket]
    exact hFB.neg_left.neg_right
  have hmiddle : IsNilpotent.exp (-F) * (B + C) * IsNilpotent.exp F = C := by
    have h := exp_mul_mul_exp_neg_eq_add_bracket (-F) (B + C) hF.neg hmiddleComm
    rw [neg_neg, hmiddleBracket] at h
    calc
      IsNilpotent.exp (-F) * (B + C) * IsNilpotent.exp F = (B + C) + -B := h
      _ = C := by abel
  have hECzero : E * C - C * E = 0 := sub_eq_zero.mpr hEC.eq
  have hlastComm : Commute E (E * C - C * E) := by
    rw [hECzero]
    exact Commute.zero_right E
  have hlast : IsNilpotent.exp E * C * IsNilpotent.exp (-E) = C := by
    simpa only [hECzero, add_zero] using
      exp_mul_mul_exp_neg_eq_add_bracket E C hE hlastComm
  calc
    IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * B *
        IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) =
      IsNilpotent.exp E *
        (IsNilpotent.exp (-F) *
          (IsNilpotent.exp E * B * IsNilpotent.exp (-E)) * IsNilpotent.exp F) *
        IsNilpotent.exp (-E) := by simp only [mul_assoc]
    _ = C := by rw [hfirst, hmiddle, hlast]

end Atlas.Algebra
