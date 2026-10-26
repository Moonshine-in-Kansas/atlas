import Atlas.Algebra.FiniteHadamard
import Atlas.Algebra.FiniteHadamardThree
import Mathlib.Tactic.Module

/-! Weyl pinning of a length-four operator string over a rational algebra.
Only the two conjugating operators are assumed nilpotent. -/

noncomputable section
namespace Atlas.Algebra
variable {S : Type*} [Ring S] [Algebra ℚ S]

theorem weyl_word_conjugate_operator_eq_sixth
    (E F B C D L : S) (hE : IsNilpotent E) (hF : IsNilpotent F)
    (hEB : E * B - B * E = C) (hEC : E * C - C * E = D)
    (hED : E * D - D * E = L) (hEL : Commute E L) (hFB : Commute F B)
    (hFC : F * C - C * F = (3 : ℚ) • B)
    (hFD : F * D - D * F = (4 : ℚ) • C)
    (hFL : F * L - L * F = (3 : ℚ) • D) :
    IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * B *
      IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) =
        (1 / 6 : ℚ) • L := by
  let B₁ := B + C + (1 / 2 : ℚ) • D + (1 / 6 : ℚ) • L
  let C₁ := (-3 : ℚ) • B + (-2 : ℚ) • C + (-1 / 2 : ℚ) • D
  let D₁ := (6 : ℚ) • B + (2 : ℚ) • C
  let L₁ := (-6 : ℚ) • B
  have hfirst : IsNilpotent.exp E * B * IsNilpotent.exp (-E) = B₁ :=
    exp_mul_mul_exp_neg_eq_add_add_half_add_sixth E B C D L hE hEB hEC hED hEL
  have hFBzero : F * B - B * F = 0 := sub_eq_zero.mpr hFB.eq
  have hmiddle₁ : (-F) * B₁ - B₁ * (-F) = C₁ := by
    calc
      _ = -(F * B - B * F) - (F * C - C * F) -
          (1 / 2 : ℚ) • (F * D - D * F) -
          (1 / 6 : ℚ) • (F * L - L * F) := by
        dsimp only [B₁]
        simp only [neg_mul, mul_neg, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, smul_sub]
        module
      _ = C₁ := by rw [hFBzero, hFC, hFD, hFL]; dsimp only [C₁]; module
  have hmiddle₂ : (-F) * C₁ - C₁ * (-F) = D₁ := by
    calc
      _ = (3 : ℚ) • (F * B - B * F) +
          (2 : ℚ) • (F * C - C * F) +
          (1 / 2 : ℚ) • (F * D - D * F) := by
        dsimp only [C₁]
        simp only [neg_mul, mul_neg, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, smul_sub]
        module
      _ = D₁ := by rw [hFBzero, hFC, hFD]; dsimp only [D₁]; module
  have hmiddle₃ : (-F) * D₁ - D₁ * (-F) = L₁ := by
    calc
      _ = (-6 : ℚ) • (F * B - B * F) + (-2 : ℚ) • (F * C - C * F) := by
        dsimp only [D₁]
        simp only [neg_mul, mul_neg, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, smul_sub]
        module
      _ = L₁ := by rw [hFBzero, hFC]; dsimp only [L₁]; module
  have hmiddleComm : Commute (-F) L₁ := by
    change (-F) * ((-6 : ℚ) • B) = ((-6 : ℚ) • B) * (-F)
    simp only [mul_smul_comm, smul_mul_assoc, neg_mul, mul_neg, hFB.eq, smul_neg]
  have hmiddle : IsNilpotent.exp (-F) * B₁ * IsNilpotent.exp F =
      (1 / 6 : ℚ) • L := by
    have h := exp_mul_mul_exp_neg_eq_add_add_half_add_sixth
      (-F) B₁ C₁ D₁ L₁ hF.neg hmiddle₁ hmiddle₂ hmiddle₃ hmiddleComm
    rw [neg_neg] at h
    calc
      _ = B₁ + C₁ + (1 / 2 : ℚ) • D₁ + (1 / 6 : ℚ) • L₁ := h
      _ = (1 / 6 : ℚ) • L := by dsimp only [B₁, C₁, D₁, L₁]; module
  have hlastBracket : E * ((1 / 6 : ℚ) • L) - ((1 / 6 : ℚ) • L) * E = 0 := by
    rw [mul_smul_comm, smul_mul_assoc, hEL.eq, sub_self]
  have hlastComm : Commute E
      (E * ((1 / 6 : ℚ) • L) - ((1 / 6 : ℚ) • L) * E) := by
    rw [hlastBracket]
    exact Commute.zero_right E
  have hlast : IsNilpotent.exp E * ((1 / 6 : ℚ) • L) * IsNilpotent.exp (-E) =
      (1 / 6 : ℚ) • L := by
    simpa only [hlastBracket, add_zero] using
      exp_mul_mul_exp_neg_eq_add_bracket E ((1 / 6 : ℚ) • L) hE hlastComm
  calc
    IsNilpotent.exp E * IsNilpotent.exp (-F) * IsNilpotent.exp E * B *
        IsNilpotent.exp (-E) * IsNilpotent.exp F * IsNilpotent.exp (-E) =
      IsNilpotent.exp E *
        (IsNilpotent.exp (-F) *
          (IsNilpotent.exp E * B * IsNilpotent.exp (-E)) * IsNilpotent.exp F) *
        IsNilpotent.exp (-E) := by simp only [mul_assoc]
    _ = (1 / 6 : ℚ) • L := by rw [hfirst, hmiddle, hlast]

end Atlas.Algebra
