import Atlas.LinearGroups.Chevalley.Comparison.F4.RootConjugation0
import Atlas.LinearGroups.Chevalley.Comparison.F4.RootConjugation1
import Atlas.LinearGroups.Chevalley.Comparison.F4.RootConjugation2
import Atlas.LinearGroups.Chevalley.Comparison.F4.RootConjugation3
import Atlas.LinearGroups.Chevalley.Comparison.F4.RootConjugation4
import Atlas.LinearGroups.Chevalley.Comparison.F4.RootConjugation5
import Atlas.LinearGroups.Chevalley.Comparison.F4.RootConjugation6
import Atlas.LinearGroups.Chevalley.Comparison.F4.RootConjugation7
import Atlas.LinearGroups.Chevalley.Comparison.F4.MatrixEmbedding
import Atlas.LinearAlgebra.QuadraticConjugation

/-! Base change of exact integer coefficient identities gives the full
parameter conjugation identity over every commutative ring. -/
namespace Atlas.Chevalley.Comparison.F4
open scoped Matrix
noncomputable section

private theorem first_identity (i : Fin 8) (j : Fin 52) :
    simpleMatrix i * basisMatrix j - basisMatrix j * simpleMatrix i =
      basisCombination (fun k => geckMatrix i k j) := by
  fin_cases i
  · exact simple_commutator_0 j
  · exact simple_commutator_1 j
  · exact simple_commutator_2 j
  · exact simple_commutator_3 j
  · exact simple_commutator_4 j
  · exact simple_commutator_5 j
  · exact simple_commutator_6 j
  · exact simple_commutator_7 j

private theorem second_identity (i : Fin 8) (j : Fin 52) :
    simpleSecondMatrix i * basisMatrix j + basisMatrix j * simpleSecondMatrix i -
      simpleMatrix i * basisMatrix j * simpleMatrix i =
        basisCombination (fun k => geckSecondMatrix i k j) := by
  fin_cases i
  · exact simple_second_conjugation_0 j
  · exact simple_second_conjugation_1 j
  · exact simple_second_conjugation_2 j
  · exact simple_second_conjugation_3 j
  · exact simple_second_conjugation_4 j
  · exact simple_second_conjugation_5 j
  · exact simple_second_conjugation_6 j
  · exact simple_second_conjugation_7 j

private theorem third_identity (i : Fin 8) (j : Fin 52) :
    simpleMatrix i * basisMatrix j * simpleSecondMatrix i -
      simpleSecondMatrix i * basisMatrix j * simpleMatrix i = 0 := by
  fin_cases i
  · exact simple_third_conjugation_0 j
  · exact simple_third_conjugation_1 j
  · exact simple_third_conjugation_2 j
  · exact simple_third_conjugation_3 j
  · exact simple_third_conjugation_4 j
  · exact simple_third_conjugation_5 j
  · exact simple_third_conjugation_6 j
  · exact simple_third_conjugation_7 j

private theorem fourth_identity (i : Fin 8) (j : Fin 52) :
    simpleSecondMatrix i * basisMatrix j * simpleSecondMatrix i = 0 := by
  fin_cases i
  · exact simple_fourth_conjugation_0 j
  · exact simple_fourth_conjugation_1 j
  · exact simple_fourth_conjugation_2 j
  · exact simple_fourth_conjugation_3 j
  · exact simple_fourth_conjugation_4 j
  · exact simple_fourth_conjugation_5 j
  · exact simple_fourth_conjugation_6 j
  · exact simple_fourth_conjugation_7 j

variable (R : Type*) [CommRing R]

def simpleOver (i : Fin 8) (t : R) : Matrix (Fin 27) (Fin 27) R :=
  1 + t • (simpleMatrix i).map (Int.castRingHom R) +
    t^2 • (simpleSecondMatrix i).map (Int.castRingHom R)

def geckOver (i : Fin 8) (t : R) : Matrix (Fin 52) (Fin 52) R :=
  1 + t • (geckMatrix i).map (Int.castRingHom R) +
    t^2 • (geckSecondMatrix i).map (Int.castRingHom R)

private theorem cast_basisCombination (v : Fin 52 → ℤ) :
    (Int.castRingHom R).mapMatrix (basisCombination v) =
      matrixEmbedding R (fun j => (v j : R)) := by
  change (Int.castRingHom R).mapMatrix (∑ j : Fin 52, v j • basisMatrix j) = _
  simp only [map_sum, map_zsmul]
  change (∑ j : Fin 52, v j • (Int.castRingHom R).mapMatrix (basisMatrix j)) =
    ∑ j : Fin 52, (v j : R) • basisOver R j
  apply Finset.sum_congr rfl
  intro j _
  rw [← Int.cast_smul_eq_zsmul R]
  simp only [basisOver, RingHom.mapMatrix_apply]

private theorem matrixEmbedding_single (j : Fin 52) :
    matrixEmbedding R (Pi.single j 1) = basisOver R j := by
  simp [matrixEmbedding, Pi.single_apply]

/-- Coefficientwise conjugation on each integral basis matrix. -/
theorem simpleOver_conjugation_basis (i : Fin 8) (j : Fin 52) (t : R) :
    simpleOver R i t * basisOver R j * simpleOver R i (-t) =
      matrixEmbedding R (fun k => geckOver R i t k j) := by
  let c := (Int.castRingHom R).mapMatrix (m := Fin 27)
  have h₁ : c (simpleMatrix i) * basisOver R j - basisOver R j * c (simpleMatrix i) =
      matrixEmbedding R (fun k => (geckMatrix i k j : R)) := by
    have h := congrArg c (first_identity i j)
    dsimp only [c] at h
    rw [cast_basisCombination R] at h
    simpa only [map_sub, map_mul, c, basisOver,
      RingHom.mapMatrix_apply] using h
  have h₂ : c (simpleSecondMatrix i) * basisOver R j + basisOver R j * c (simpleSecondMatrix i) -
      c (simpleMatrix i) * basisOver R j * c (simpleMatrix i) =
        matrixEmbedding R (fun k => (geckSecondMatrix i k j : R)) := by
    have h := congrArg c (second_identity i j)
    dsimp only [c] at h
    rw [cast_basisCombination R] at h
    simpa only [map_sub, map_add, map_mul, c, basisOver,
      RingHom.mapMatrix_apply] using h
  have h₃ : c (simpleMatrix i) * basisOver R j * c (simpleSecondMatrix i) -
      c (simpleSecondMatrix i) * basisOver R j * c (simpleMatrix i) = 0 := by
    have h := congrArg c (third_identity i j)
    simpa only [map_sub, map_mul, map_zero, c, basisOver, RingHom.mapMatrix_apply] using h
  have h₄ : c (simpleSecondMatrix i) * basisOver R j * c (simpleSecondMatrix i) = 0 := by
    have h := congrArg c (fourth_identity i j)
    simpa only [map_mul, map_zero, c, basisOver, RingHom.mapMatrix_apply] using h
  rw [show simpleOver R i t = 1+t • c (simpleMatrix i)+t^2 • c (simpleSecondMatrix i) from rfl,
    show simpleOver R i (-t) = 1+(-t) • c (simpleMatrix i)+(-t)^2 • c (simpleSecondMatrix i) from rfl]
  rw [Atlas.LinearAlgebra.quadratic_conjugation_of_coefficients
    _ _ _ _ _ _ h₁ h₂ h₃ h₄, smul_zero, add_zero]
  rw [← matrixEmbedding_single R j, ← map_smul, ← map_smul, ← map_add, ← map_add]
  apply congrArg (matrixEmbedding R)
  funext k
  simp [geckOver, Pi.single_apply, Matrix.one_apply, smul_eq_mul, eq_comm]

/-- The full 52-coordinate action is intertwined by actual 27-coordinate
conjugation, uniformly without excluding any field characteristic. -/
theorem simpleOver_conjugation (i : Fin 8) (t : R) (v : Fin 52 → R) :
    simpleOver R i t * matrixEmbedding R v * simpleOver R i (-t) =
      matrixEmbedding R (geckOver R i t *ᵥ v) := by
  calc
    _ = ∑ j : Fin 52, v j •
        (simpleOver R i t * basisOver R j * simpleOver R i (-t)) := by
      simp [matrixEmbedding, Finset.mul_sum, Finset.sum_mul,
        mul_smul_comm, smul_mul_assoc]
    _ = ∑ j : Fin 52, v j • matrixEmbedding R (fun k => geckOver R i t k j) := by
      simp_rw [simpleOver_conjugation_basis]
    _ = matrixEmbedding R (∑ j : Fin 52, v j • (fun k => geckOver R i t k j)) := by
      simp only [map_sum, map_smul]
    _ = _ := by
      apply congrArg (matrixEmbedding R)
      funext k
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

end
end Atlas.Chevalley.Comparison.F4
