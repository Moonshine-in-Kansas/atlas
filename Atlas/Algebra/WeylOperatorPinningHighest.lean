import Atlas.Algebra.WeylOperatorPinning
import Mathlib.Tactic.NoncommRing

/-! The other endpoint of a length-two nilpotent operator string. -/
noncomputable section
namespace Atlas.Algebra
variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- In the same length-two string as the existing low-to-high pinning,
the positive Weyl word sends the highest operator to minus the lowest. -/
theorem weyl_word_conjugate_highest_eq_neg
    (E F B C : S) (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEB : E * B - B * E = C) (hEC : Commute E C)
    (hFB : Commute F B) (hFC : F * C - C * F = B) :
    IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * C *
      IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) = -B := by
  have hECzero : E * C - C * E = 0 := sub_eq_zero.mpr hEC.eq
  have hfirst : IsNilpotent.exp E * C * IsNilpotent.exp (-E) = C := by
    have hcomm : Commute E (E * C - C * E) := by
      rw [hECzero]
      exact Commute.zero_right E
    simpa only [hECzero, add_zero] using exp_mul_mul_exp_neg_eq_add_bracket E C hE hcomm
  have hmiddleBracket : (-F) * C - C * (-F) = -B := by
    calc
      (-F) * C - C * (-F) = -(F * C - C * F) := by noncomm_ring
      _ = -B := congrArg Neg.neg hFC
  have hmiddleComm : Commute (-F) ((-F) * C - C * (-F)) := by
    rw [hmiddleBracket]
    exact hFB.neg_left.neg_right
  have hmiddle : IsNilpotent.exp (-F) * C * IsNilpotent.exp F = C - B := by
    have h := exp_mul_mul_exp_neg_eq_add_bracket (-F) C hF.neg hmiddleComm
    simpa only [neg_neg, hmiddleBracket, sub_eq_add_neg] using h
  have hlastBracket : E * (C - B) - (C - B) * E = -C := by
    calc
      E * (C - B) - (C - B) * E = (E * C - C * E) - (E * B - B * E) := by
        noncomm_ring
      _ = -C := by rw [hECzero, hEB, zero_sub]
  have hlastComm : Commute E (E * (C - B) - (C - B) * E) := by
    rw [hlastBracket]
    exact hEC.neg_right
  have hlast : IsNilpotent.exp E * (C - B) * IsNilpotent.exp (-E) = -B := by
    have h := exp_mul_mul_exp_neg_eq_add_bracket E (C - B) hE hlastComm
    rw [hlastBracket] at h
    calc
      IsNilpotent.exp E * (C - B) * IsNilpotent.exp (-E) = C - B + -C := h
      _ = -B := by abel
  calc
    _ = IsNilpotent.exp E *
        (IsNilpotent.exp (-F) *
          (IsNilpotent.exp E * C * IsNilpotent.exp (-E)) * IsNilpotent.exp F) *
        IsNilpotent.exp (-E) := by simp only [mul_assoc]
    _ = -B := by rw [hfirst, hmiddle, hlast]

end Atlas.Algebra
