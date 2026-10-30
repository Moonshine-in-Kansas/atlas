import Atlas.LinearGroups.Chevalley.Comparison.G2.IntegralBasisInjection
import Atlas.LinearGroups.Chevalley.Comparison.G2.ActualGeckMatrices
import Atlas.LinearAlgebra.QuadraticConjugation

/-! The integral Geck module inside octonion endomorphisms, including the bad
characteristics. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.G2
open Classical
open scoped Matrix
variable (R : Type*) [CommRing R]

def basisOver (j : Fin 14) : Matrix (Fin 8) (Fin 8) R :=
  (basisMatrix j).map (Int.castRingHom R)

def gamma : (Fin 14 → R) →ₗ[R] Matrix (Fin 8) (Fin 8) R where
  toFun v := ∑ j, v j • basisOver R j
  map_add' v w := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t v := by simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

theorem gamma_single (j : Fin 14) : gamma R (Pi.single j 1) = basisOver R j := by
  simp [gamma, Pi.single_apply]

def readLinear : Matrix (Fin 8) (Fin 8) R →ₗ[R] (Fin 14 → R) where
  toFun := readCoordinates
  map_add' a b := by
    ext i
    fin_cases i <;> norm_num [readCoordinates, rootPivot] <;> ring
  map_smul' t a := by
    ext i
    fin_cases i <;> norm_num [readCoordinates, rootPivot] <;> ring

theorem readLinear_basis (j : Fin 14) : readLinear R (basisOver R j) = Pi.single j 1 := by
  ext i
  have h := congrArg (Int.castRingHom R) (readCoordinates_basis i j)
  change readCoordinates (basisOver R j) i = (Pi.single j (1 : R) : Fin 14 → R) i
  fin_cases i <;>
    simpa [readCoordinates, rootPivot, basisOver, Matrix.map_apply, Matrix.cons_val,
      Pi.single_apply, eq_comm, apply_ite, Int.cast_add, Int.cast_mul, Int.cast_neg] using h

theorem readLinear_gamma (v : Fin 14 → R) : readLinear R (gamma R v) = v := by
  change readLinear R (∑ j, v j • basisOver R j) = v
  rw [map_sum]
  simp_rw [map_smul, readLinear_basis]
  ext i
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

theorem gamma_injective : Function.Injective (gamma R) :=
  Function.LeftInverse.injective (readLinear_gamma R)

theorem basisCombination_map (v : Fin 14 → ℤ) :
    (basisCombination v).map (Int.castRingHom R) = gamma R (fun j => (v j : R)) := by
  ext r c
  change (Int.castRingHom R) ((∑ j, v j • basisMatrix j) r c) =
    (∑ j, (v j : R) • (basisMatrix j).map (Int.castRingHom R)) r c
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]
  simp [smul_eq_mul]

def simpleExponential (i : Fin 4) (t : R) : Matrix (Fin 8) (Fin 8) R :=
  1 + t • (simpleMatrix i).map (Int.castRingHom R) +
    t^2 • (simpleSecondMatrix i).map (Int.castRingHom R)

private theorem integral_c1 (i : Fin 4) (j : Fin 14) :
    simpleMatrix i * basisMatrix j - basisMatrix j * simpleMatrix i =
      basisCombination (fun k => geckMatrix i k j) := by
  fin_cases i
  · exact simple_commutator_0 j
  · exact simple_commutator_1 j
  · exact simple_commutator_2 j
  · exact simple_commutator_3 j

private theorem integral_c2 (i : Fin 4) (j : Fin 14) :
    simpleSecondMatrix i * basisMatrix j + basisMatrix j * simpleSecondMatrix i -
        simpleMatrix i * basisMatrix j * simpleMatrix i =
      basisCombination (fun k => geckSecondMatrix i k j) := by
  fin_cases i
  · exact simple_second_conjugation_0 j
  · exact simple_second_conjugation_1 j
  · exact simple_second_conjugation_2 j
  · exact simple_second_conjugation_3 j

private theorem integral_c3 (i : Fin 4) (j : Fin 14) :
    simpleMatrix i * basisMatrix j * simpleSecondMatrix i -
        simpleSecondMatrix i * basisMatrix j * simpleMatrix i =
      basisCombination (fun k => geckThirdMatrix i k j) := by
  fin_cases i
  · exact simple_third_conjugation_0 j
  · exact simple_third_conjugation_1 j
  · exact simple_third_conjugation_2 j
  · exact simple_third_conjugation_3 j

private theorem integral_c4 (i : Fin 4) (j : Fin 14) :
    simpleSecondMatrix i * basisMatrix j * simpleSecondMatrix i = 0 := by
  fin_cases i
  · exact simple_fourth_conjugation_0 j
  · exact simple_fourth_conjugation_1 j
  · exact simple_fourth_conjugation_2 j
  · exact simple_fourth_conjugation_3 j

theorem conjugation_basis (i : Fin 4) (j : Fin 14) (t : R) :
    simpleExponential R i t * basisOver R j * simpleExponential R i (-t) =
      gamma R (geckExponential R i t *ᵥ Pi.single j 1) := by
  have h1 := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℤ =>
    A.map (Int.castRingHom R)) (integral_c1 i j)
  have h2 := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℤ =>
    A.map (Int.castRingHom R)) (integral_c2 i j)
  have h3 := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℤ =>
    A.map (Int.castRingHom R)) (integral_c3 i j)
  have h4 := congrArg (fun A : Matrix (Fin 8) (Fin 8) ℤ =>
    A.map (Int.castRingHom R)) (integral_c4 i j)
  simp only [Matrix.map_mul,
    Matrix.map_add (Int.castRingHom R) (map_add (Int.castRingHom R)),
    Matrix.map_sub (Int.castRingHom R) (map_sub (Int.castRingHom R)),
    basisCombination_map] at h1 h2 h3
  simp only [Matrix.map_mul,
    Matrix.map_zero (Int.castRingHom R) (map_zero (Int.castRingHom R))] at h4
  rw [simpleExponential, simpleExponential, basisOver,
    Atlas.LinearAlgebra.quadratic_conjugation_of_coefficients _ _ _ _ _ _ h1 h2 h3 h4]
  simp only [geckExponential, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, map_add, map_smul, gamma_single, basisOver]
  simp only [Matrix.mulVec_single_one, Matrix.col_apply', Matrix.map_apply,
    Int.coe_castRingHom]

theorem conjugation_gamma (i : Fin 4) (t : R) (v : Fin 14 → R) :
    simpleExponential R i t * gamma R v * simpleExponential R i (-t) =
      gamma R (geckExponential R i t *ᵥ v) := by
  have hv : v = ∑ j : Fin 14, v j • Pi.single j 1 := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul]
  change simpleExponential R i t * (∑ j, v j • basisOver R j) *
    simpleExponential R i (-t) = _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, smul_mul_assoc, conjugation_basis]

end Atlas.Chevalley.Comparison.G2
