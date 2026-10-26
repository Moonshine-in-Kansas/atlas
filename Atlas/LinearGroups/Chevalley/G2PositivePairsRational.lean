import Atlas.LinearGroups.Chevalley.ConjugatedRootExponential
import Atlas.LinearGroups.Chevalley.G2PositiveOperatorPinning

/-! Source candidate: the three two-step commutators and all ten commuting
unordered distinct positive-root pairs in a literal G2 simple plane.
The simple pair and the two short roots at 120 degrees are separate. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]
include hdiamond

/-- Thirteen of the fifteen unordered distinct pairs, with literal Weyl
representatives. The other two pairs are (A,B) and (A,Z). -/
theorem adjoint_g2_positive_pairs_twoStep_and_commute_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (s t : R) :
    let ni := adjointWeyl P b R i 1
    let nj := adjointWeyl P b R j 1
    let Z (u : R) := nj * adjointX P b R i u * nj⁻¹
    let W (u : R) := (ni * nj) * adjointX P b R i u * (ni * nj)⁻¹
    let V (u : R) := ni * adjointX P b R j u * ni⁻¹
    let H (u : R) := (nj * ni) * adjointX P b R j u * (nj * ni)⁻¹
    ⁅adjointX P b R i s, W t⁆ = V (3*s*t) ∧
    ⁅adjointX P b R j s, V t⁆ = H (s*t) ∧
    ⁅Z s, W t⁆ = H (3*s*t) ∧
    Commute (adjointX P b R i s) (V t) ∧
    Commute (adjointX P b R i s) (H t) ∧
    Commute (adjointX P b R j s) (Z t) ∧
    Commute (adjointX P b R j s) (W t) ∧
    Commute (adjointX P b R j s) (H t) ∧
    Commute (Z s) (V t) ∧ Commute (Z s) (H t) ∧
    Commute (W s) (V t) ∧ Commute (W s) (H t) ∧ Commute (V s) (H t) := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A * B - B * A
  let D := A * C - C * A
  let L := A * D - D * A
  let F := B * L - L * B
  let ni := adjointWeyl P b R i 1
  let nj := adjointWeyl P b R j 1
  let E (u : Adjoint P b R) (k : b.support) :=
    u.val.val * raisingOver P b R k * (u⁻¹).val.val
  obtain ⟨hAL,hBC,hBD,hCD,hCL,hDL,hAF,hBF,hCF,hDF,hLF⟩ :=
    raisingOver_g2_cross_brackets P b hdiamond R i j hne hij hji
  change C*D-D*C = -F at hCD
  have hpin := adjointWeyl_g2_positive_operator_pinnings P b hdiamond R i j hne hij hji
  change E nj i = -C ∧ E (ni*nj) i = (1/2:ℚ) • D ∧
    E ni j = (1/6:ℚ) • L ∧ E (nj*ni) j = (1/6:ℚ) • F at hpin
  obtain ⟨hZ,hW,hV,hH⟩ := hpin
  have hA : E 1 i = A := by simp [E,A]
  have hB : E 1 j = B := by simp [E,B]
  have hAW : E 1 i * E (ni*nj) i - E (ni*nj) i * E 1 i = (3:R) • E ni j := by
    rw [hA,hW,hV,mul_smul_comm,smul_mul_assoc,← smul_sub]
    change (1/2:ℚ) • L = (3:R) • ((1/6:ℚ) • L)
    rw [show (3:R) = 1+1+1 by ring]
    simp only [add_smul,one_smul]
    module
  have hBV : E 1 j * E ni j - E ni j * E 1 j = (1:R) • E (nj*ni) j := by
    rw [hB,hV,hH,one_smul,mul_smul_comm,smul_mul_assoc,← smul_sub]
  have hZW : E nj i * E (ni*nj) i - E (ni*nj) i * E nj i = (3:R) • E (nj*ni) j := by
    rw [hZ,hW,hH]
    calc
      (-C) * ((1/2:ℚ) • D) - ((1/2:ℚ) • D) * (-C) =
          (-1/2:ℚ) • (C*D-D*C) := by
        simp only [neg_mul,mul_neg,mul_smul_comm,smul_mul_assoc,smul_sub]
        module
      _ = (3:R) • ((1/6:ℚ) • F) := by
        rw [hCD,show (3:R) = 1+1+1 by ring]
        simp only [add_smul,one_smul]
        module
  have step (u v w : Adjoint P b R) (a b' c : b.support) (r : R)
      (hbr : E u a * E v b' - E v b' * E u a = r • E w c)
      (hl : Commute (E u a) (E w c)) (hr : Commute (E v b') (E w c)) :=
    adjoint_conjugateX_commutator_of_operator_twoStep P b R u v w a b' c r hbr hl hr s t
  have com (u v : Adjoint P b R) (a b' : b.support)
      (h : Commute (E u a) (E v b')) :=
    adjoint_conjugateX_commute_of_operator_commute P b R u v a b' h s t
  have hAVL : Commute (E 1 i) (E ni j) := by
    rw [hA,hV]; exact hAL.smul_right _
  have hWVL : Commute (E (ni*nj) i) (E ni j) := by
    rw [hW,hV]; exact (hDL.smul_left _).smul_right _
  have hBHL : Commute (E 1 j) (E (nj*ni) j) := by
    rw [hB,hH]; exact hBF.smul_right _
  have hVHL : Commute (E ni j) (E (nj*ni) j) := by
    rw [hV,hH]; exact (hLF.smul_left _).smul_right _
  have hZHL : Commute (E nj i) (E (nj*ni) j) := by
    rw [hZ,hH]; exact hCF.neg_left.smul_right _
  have hWHL : Commute (E (ni*nj) i) (E (nj*ni) j) := by
    rw [hW,hH]; exact (hDF.smul_left _).smul_right _
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [one_mul,mul_one,inv_one] using step 1 (ni*nj) ni i i j 3 hAW hAVL hWVL
  · simpa only [one_mul,mul_one,inv_one] using step 1 ni (nj*ni) j j j 1 hBV hBHL hVHL
  · exact step nj (ni*nj) (nj*ni) i i j 3 hZW hZHL hWHL
  · simpa only [one_mul,mul_one,inv_one] using com 1 ni i j hAVL
  · have h : Commute (E 1 i) (E (nj*ni) j) := by
      rw [hA,hH]; exact hAF.smul_right _
    simpa only [one_mul,mul_one,inv_one] using com 1 (nj*ni) i j h
  · have h : Commute (E 1 j) (E nj i) := by
      rw [hB,hZ]; exact hBC.neg_right
    simpa only [one_mul,mul_one,inv_one] using com 1 nj j i h
  · have h : Commute (E 1 j) (E (ni*nj) i) := by
      rw [hB,hW]; exact hBD.smul_right _
    simpa only [one_mul,mul_one,inv_one] using com 1 (ni*nj) j i h
  · simpa only [one_mul,mul_one,inv_one] using com 1 (nj*ni) j j hBHL
  · have h : Commute (E nj i) (E ni j) := by
      rw [hZ,hV]; exact hCL.neg_left.smul_right _
    exact com nj ni i j h
  · exact com nj (nj*ni) i j hZHL
  · exact com (ni*nj) ni i j hWVL
  · exact com (ni*nj) (nj*ni) i j hWHL
  · exact com ni (nj*ni) j j hVHL

end Atlas.Chevalley
