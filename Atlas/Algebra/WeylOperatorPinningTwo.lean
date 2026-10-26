import Atlas.Algebra.FiniteHadamard
import Atlas.Algebra.FiniteHadamardTwo
import Mathlib.Tactic.Module

/-! UNCOMPILED source candidate. The length-three Weyl operator string.
Rational denominators occur only in this characteristic-zero intermediate. -/

noncomputable section
namespace Atlas.Algebra

variable {S : Type*} [Ring S] [Algebra ℚ S]

/-- The Weyl word exp(E)exp(-F)exp(E) sends the bottom of an actual
length-three sl2 string to half its twice-raised operator. The hypotheses
are explicit operator equalities, not a representation or group assumption. -/
theorem weyl_word_conjugate_operator_eq_half
    (E F B C D : S) (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEB : E * B - B * E = C) (hEC : E * C - C * E = D)
    (hED : Commute E D) (hFB : Commute F B)
    (hFC : F * C - C * F = (2 : ℚ) • B)
    (hFD : F * D - D * F = (2 : ℚ) • C) :
    IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * B *
      IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) =
        (1 / 2 : ℚ) • D := by
  have hfirst : IsNilpotent.exp E * B * IsNilpotent.exp (-E) =
      B + C + (1 / 2 : ℚ) • D :=
    exp_mul_mul_exp_neg_eq_add_add_half E B C D hE hEB hEC hED
  have hFBzero : F * B - B * F = 0 := sub_eq_zero.mpr hFB.eq
  have hmiddleBracket :
      (-F) * (B + C + (1 / 2 : ℚ) • D) -
        (B + C + (1 / 2 : ℚ) • D) * (-F) = (-2 : ℚ) • B - C := by
    calc
      (-F) * (B + C + (1 / 2 : ℚ) • D) -
          (B + C + (1 / 2 : ℚ) • D) * (-F) =
          -(F * B - B * F) - (F * C - C * F) -
            (1 / 2 : ℚ) • (F * D - D * F) := by
        simp only [neg_mul, mul_neg, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, smul_sub]
        module
      _ = (-2 : ℚ) • B - C := by rw [hFBzero, hFC, hFD]; module
  have hmiddleSecond :
      (-F) * ((-2 : ℚ) • B - C) - ((-2 : ℚ) • B - C) * (-F) =
        (2 : ℚ) • B := by
    calc
      (-F) * ((-2 : ℚ) • B - C) - ((-2 : ℚ) • B - C) * (-F) =
          (2 : ℚ) • (F * B - B * F) + (F * C - C * F) := by
        simp only [neg_mul, mul_neg, mul_sub, sub_mul,
          mul_smul_comm, smul_mul_assoc, smul_sub]
        module
      _ = (2 : ℚ) • B := by rw [hFBzero, hFC]; module
  have hmiddleComm : Commute (-F) ((2 : ℚ) • B) := by
    change (-F) * ((2 : ℚ) • B) = ((2 : ℚ) • B) * (-F)
    simp only [mul_smul_comm, smul_mul_assoc, neg_mul, mul_neg, hFB.eq, smul_neg]
  have hmiddle : IsNilpotent.exp (-F) * (B + C + (1 / 2 : ℚ) • D) *
      IsNilpotent.exp F = (1 / 2 : ℚ) • D := by
    have h := exp_mul_mul_exp_neg_eq_add_add_half (-F)
      (B + C + (1 / 2 : ℚ) • D) ((-2 : ℚ) • B - C) ((2 : ℚ) • B)
      hF.neg hmiddleBracket hmiddleSecond hmiddleComm
    rw [neg_neg] at h
    calc
      IsNilpotent.exp (-F) * (B + C + (1 / 2 : ℚ) • D) *
          IsNilpotent.exp F =
          (B + C + (1 / 2 : ℚ) • D) + ((-2 : ℚ) • B - C) +
            (1 / 2 : ℚ) • ((2 : ℚ) • B) := h
      _ = (1 / 2 : ℚ) • D := by module
  have hlastBracket : E * ((1 / 2 : ℚ) • D) - ((1 / 2 : ℚ) • D) * E = 0 := by
    rw [mul_smul_comm, smul_mul_assoc, hED.eq, sub_self]
  have hlastComm : Commute E
      (E * ((1 / 2 : ℚ) • D) - ((1 / 2 : ℚ) • D) * E) := by
    rw [hlastBracket]
    exact Commute.zero_right E
  have hlast : IsNilpotent.exp E * ((1 / 2 : ℚ) • D) *
      IsNilpotent.exp (-E) = (1 / 2 : ℚ) • D := by
    simpa only [hlastBracket, add_zero] using
      exp_mul_mul_exp_neg_eq_add_bracket E ((1 / 2 : ℚ) • D) hE hlastComm
  calc
    IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * B *
        IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) =
      IsNilpotent.exp E *
        (IsNilpotent.exp (-F) *
          (IsNilpotent.exp E * B * IsNilpotent.exp (-E)) * IsNilpotent.exp F) *
        IsNilpotent.exp (-E) := by simp only [mul_assoc]
    _ = (1 / 2 : ℚ) • D := by rw [hfirst, hmiddle, hlast]

end Atlas.Algebra
