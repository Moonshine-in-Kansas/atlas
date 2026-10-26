import Atlas.LinearGroups.Chevalley.Integral.RootString
import Atlas.LinearGroups.Chevalley.RankOne
import Atlas.LinearGroups.Chevalley.Integral.StringWeyl
import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fin.Rev

noncomputable section
namespace Atlas.Chevalley.Integral
open RootPairing.GeckConstruction
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The actual rectangular inclusion matrix for a complete root string. -/
def geckStringMatrix (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    Matrix (b.support ⊕ ι) (Fin (geckStringLength P i j+1)) ℤ :=
  LinearMap.toMatrix Finsupp.basisSingleOne (Pi.basisFun ℤ _)
    (geckStringMap P b i j h)

omit [P.IsReduced] in
theorem geckStringMatrix_entry (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (row : b.support ⊕ ι)
    (k : Fin (geckStringLength P i j+1)) :
    geckStringMatrix P b i j h row k = v b (geckStringIndex P i j h k) row := by
  rw [geckStringMatrix, LinearMap.toMatrix_apply]
  change geckStringMap P b i j h (Finsupp.single k 1) row = _
  rw [geckStringMap_single, one_smul]

theorem geckStringMatrix_divided (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (n : ℕ) :
    raisingDividedPower P b i n * geckStringMatrix P b i j h =
      geckStringMatrix P b i j h * stringDividedMatrix (geckStringLength P i j) n := by
  have hl : (raisingDividedPower P b i n).mulVecLin.comp (geckStringMap P b i j h) =
      (geckStringMap P b i j h).comp (stringDividedPower (geckStringLength P i j) n) :=
    LinearMap.ext (geckString_dividedPower P b i j h n)
  have hm := congrArg
    (LinearMap.toMatrix Finsupp.basisSingleOne (Pi.basisFun ℤ (b.support ⊕ ι))) hl
  rw [LinearMap.toMatrix_comp Finsupp.basisSingleOne (Pi.basisFun ℤ _) (Pi.basisFun ℤ _),
    LinearMap.toMatrix_comp Finsupp.basisSingleOne Finsupp.basisSingleOne (Pi.basisFun ℤ _)] at hm
  simpa only [geckStringMatrix, LinearMap.toMatrix_eq_toMatrix',
    ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', ← stringDividedMatrix_eq_toMatrix] using hm

variable (R : Type*) [CommRing R]

/-- Scalar reduction of the actual integral root-string inclusion. -/
def geckStringMatrixOver (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) :
    Matrix (b.support ⊕ ι) (Fin (geckStringLength P i j+1)) R :=
  (geckStringMatrix P b i j h).map (Int.castRingHom R)

theorem geckStringMatrixOver_divided (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (n : ℕ) :
    raisingDividedOver P b R i n * geckStringMatrixOver P b R i j h =
      geckStringMatrixOver P b R i j h * stringDividedMatrix (geckStringLength P i j) n := by
  have hm := congrArg (fun A => A.map (Int.castRingHom R))
    (geckStringMatrix_divided P b i j h n)
  simpa only [Matrix.map_mul, stringDividedMatrix_map,
    raisingDividedOver, geckStringMatrixOver] using hm

theorem stringDividedMatrix_eq_zero_of_lt (n k : ℕ) (hk : n < k) :
    (stringDividedMatrix n k : Matrix _ _ R) = 0 := by
  ext i j
  have h : i.val ≠ j.val+k := by omega
  simp [stringDividedMatrix, h]

theorem stringExponential_eq_sum_four (n : ℕ) (hn : n ≤ 3) (t : R) :
    stringExponential n t = ∑ k ∈ Finset.range 4, t^k • stringDividedMatrix n k := by
  rw [stringExponential_eq_sum]
  apply Finset.sum_subset
  · exact Finset.range_mono (by omega)
  · intro k hk hk'
    have hn' : n < k := by simp only [Finset.mem_range] at hk'; omega
    rw [stringDividedMatrix_eq_zero_of_lt R n k hn', smul_zero]

/-- Actual Geck root exponentials intertwine with the already checked binomial
string exponentials, over every commutative coefficient ring. -/
theorem geckStringMatrixOver_exponential (i : b.support) (j : ι)
    (h : LinearIndependent ℤ ![P.root i, P.root j]) (t : R) :
    raisingExponential P b R i t * geckStringMatrixOver P b R i j h =
      geckStringMatrixOver P b R i j h * stringExponential (geckStringLength P i j) t := by
  rw [raisingExponential, stringExponential_eq_sum_four R _
    (geckStringLength_le_three P i j)]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [geckStringMatrixOver_divided]

end Atlas.Chevalley.Integral
