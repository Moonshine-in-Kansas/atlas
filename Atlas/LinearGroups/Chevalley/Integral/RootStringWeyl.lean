import Atlas.LinearGroups.Chevalley.Integral.RootStringExponential
import Atlas.LinearGroups.Chevalley.Integral.RootStringReflection
import Atlas.LinearGroups.Chevalley.RankOne
import Atlas.LinearGroups.Chevalley.Integral.StringWeyl
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section
namespace Atlas.Chevalley.Integral
open RootPairing.GeckConstruction
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- Reverse the integral divided-power matrix to obtain the lowering coefficients. -/
def stringLowerDividedMatrix (n k : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.reindexRingEquiv R Fin.revPerm (stringDividedMatrix n k)

theorem stringLowerDividedMatrix_entry (n k : ℕ) (i j : Fin (n+1)) :
    stringLowerDividedMatrix R n k i j = stringDividedMatrix n k i.rev j.rev := rfl

theorem stringLowering_eq_matrix (n : ℕ) :
    LinearMap.toMatrix Finsupp.basisSingleOne Finsupp.basisSingleOne (stringLowering n) =
      stringLowerDividedMatrix ℤ n 1 := by
  ext i j
  rw [LinearMap.toMatrix_apply, stringLowerDividedMatrix_entry]
  change stringLowering n (Finsupp.single j 1) i = _
  rw [stringLowering_single, one_smul]
  simp only [stringDividedMatrix]
  by_cases hj : j.val = 0
  · have hz : ¬ i.rev.val = j.rev.val+1 := by simp only [Fin.val_rev] at *; omega
    rw [ite_eq_left hj, ite_eq_right hz]
    rfl
  · have hj' : j.val-1 < n+1 := by omega
    have he : i.rev.val = j.rev.val+1 ↔ i.val = j.val-1 := by
      simp only [Fin.val_rev]
      omega
    by_cases hi : i.val = j.val-1
    · have hi' : i = (⟨j.val-1,hj'⟩ : Fin (n+1)) := Fin.ext hi
      have hc : i.rev.val = n-j.val+1 := by simp only [Fin.val_rev]; omega
      rw [ite_eq_right hj, ite_eq_left (he.mpr hi), Nat.choose_one_right, hc]
      simp [stringBasis, hj', hi']
    · rw [ite_eq_right hj, ite_eq_right (fun hh => hi (he.mp hh))]
      simp [stringBasis, hj', Fin.ext_iff, hi]

theorem factorial_smul_stringLowerDividedMatrix (n k : ℕ) :
    (k.factorial : ℤ) • stringLowerDividedMatrix ℤ n k =
      stringLowerDividedMatrix ℤ n 1 ^ k := by
  have hm := congrArg
    (LinearMap.toMatrix (Finsupp.basisSingleOne : Module.Basis (Fin (n+1)) ℤ (StringLattice n))
      Finsupp.basisSingleOne) (factorial_smul_stringDividedPower n k)
  rw [map_smul, ← LinearMap.toMatrix_pow] at hm
  rw [← stringDividedPower_one n, ← stringDividedMatrix_eq_toMatrix,
    ← stringDividedMatrix_eq_toMatrix] at hm
  have hr := congrArg (Matrix.reindexRingEquiv ℤ (Fin.revPerm : Equiv.Perm (Fin (n+1)))) hm
  simpa only [map_zsmul, map_pow, stringLowerDividedMatrix] using hr

omit [P.IsReduced] in
theorem geckStringMatrix_lowering (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    lowering P b i * geckStringMatrix P b i j h =
      geckStringMatrix P b i j h * stringLowerDividedMatrix ℤ (geckStringLength P i j) 1 := by
  have hm := congrArg
    (LinearMap.toMatrix Finsupp.basisSingleOne (Pi.basisFun ℤ (b.support ⊕ ι)))
    (geckString_lowering P b i j h)
  rw [LinearMap.toMatrix_comp Finsupp.basisSingleOne (Pi.basisFun ℤ _) (Pi.basisFun ℤ _),
    LinearMap.toMatrix_comp Finsupp.basisSingleOne Finsupp.basisSingleOne (Pi.basisFun ℤ _)] at hm
  simpa only [geckStringMatrix, LinearMap.toMatrix_eq_toMatrix',
    ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', stringLowering_eq_matrix] using hm

omit [P.IsReduced] in
theorem geckStringMatrix_lowering_pow (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (k : ℕ) :
    lowering P b i ^ k * geckStringMatrix P b i j h =
      geckStringMatrix P b i j h * stringLowerDividedMatrix ℤ (geckStringLength P i j) 1 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, geckStringMatrix_lowering,
      Matrix.mul_assoc, ← pow_succ']

theorem geckStringMatrix_lowerDivided (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (k : ℕ) :
    loweringDividedPower P b i k * geckStringMatrix P b i j h =
      geckStringMatrix P b i j h * stringLowerDividedMatrix ℤ (geckStringLength P i j) k := by
  apply (smul_right_injective
    (M := Matrix (b.support ⊕ ι) (Fin (geckStringLength P i j+1)) ℤ)
    (by exact_mod_cast Nat.factorial_ne_zero k : (k.factorial : ℤ) ≠ 0))
  dsimp only
  rw [← Matrix.smul_mul, factorial_smul_loweringDividedPower, geckStringMatrix_lowering_pow,
    ← factorial_smul_stringLowerDividedMatrix, Matrix.mul_smul]

theorem stringLowerDividedMatrix_map (n k : ℕ) :
    (stringLowerDividedMatrix ℤ n k).map (Int.castRingHom R) =
      stringLowerDividedMatrix R n k := by
  ext i j
  simp only [Matrix.map_apply, stringLowerDividedMatrix_entry]
  exact congrArg (fun A => A i.rev j.rev) (stringDividedMatrix_map (R := R) n k)

theorem geckStringMatrixOver_lowerDivided (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (k : ℕ) :
    (loweringDividedPower P b i k).map (Int.castRingHom R) * geckStringMatrixOver P b R i j h =
      geckStringMatrixOver P b R i j h * stringLowerDividedMatrix R (geckStringLength P i j) k := by
  have hm := congrArg (fun A => A.map (Int.castRingHom R))
    (geckStringMatrix_lowerDivided P b i j h k)
  simpa only [Matrix.map_mul, stringLowerDividedMatrix_map, geckStringMatrixOver] using hm


theorem geckStringMatrixOver_lowerExponential (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (t : R) :
    loweringExponential P b R i t * geckStringMatrixOver P b R i j h =
      geckStringMatrixOver P b R i j h *
        (stringExponential (geckStringLength P i j) t).submatrix Fin.rev Fin.rev := by
  have he : (stringExponential (geckStringLength P i j) t).submatrix Fin.rev Fin.rev =
      ∑ k ∈ Finset.range 4, t^k • stringLowerDividedMatrix R (geckStringLength P i j) k := by
    rw [stringExponential_eq_sum_four R _ (geckStringLength_le_three P i j)]
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
      stringLowerDividedMatrix_entry]
  rw [loweringExponential, he]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [geckStringMatrixOver_lowerDivided]

/-- Full opposite-root words intertwine with the same finite string operators.
The Weyl representative follows by substituting (t,−t⁻¹,t). -/
theorem geckStringMatrixOver_opposite_word (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (a c d : R) :
    (raisingExponential P b R i a * loweringExponential P b R i c *
      raisingExponential P b R i d) * geckStringMatrixOver P b R i j h =
      geckStringMatrixOver P b R i j h *
        (stringExponential (geckStringLength P i j) a *
          (stringExponential (geckStringLength P i j) c).submatrix Fin.rev Fin.rev *
          stringExponential (geckStringLength P i j) d) := by
  rw [Matrix.mul_assoc, geckStringMatrixOver_exponential, ← Matrix.mul_assoc,
    Matrix.mul_assoc (raisingExponential P b R i a), geckStringMatrixOver_lowerExponential,
    ← Matrix.mul_assoc, geckStringMatrixOver_exponential]
  simp only [Matrix.mul_assoc]


/-- The actual Weyl element of the generated adjoint group acts by the finite
string Weyl word; no abstract representation or recognition theorem is used. -/
theorem geckStringMatrixOver_weyl (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (t : Rˣ) :
    (Atlas.Chevalley.adjointWeyl P b R i t).val.val * geckStringMatrixOver P b R i j h =
      geckStringMatrixOver P b R i j h *
        (stringExponential (geckStringLength P i j) t.val *
          (stringExponential (geckStringLength P i j) (-t.inv)).submatrix Fin.rev Fin.rev *
          stringExponential (geckStringLength P i j) t.val) := by
  change (raisingExponential P b R i t.val * (loweringRootElement P b R i (-t.inv)).val *
    raisingExponential P b R i t.val) * geckStringMatrixOver P b R i j h = _
  rw [loweringRootElement_val]
  exact geckStringMatrixOver_opposite_word P b R i j h t.val (-t.inv) t.val

end Atlas.Chevalley.Integral
