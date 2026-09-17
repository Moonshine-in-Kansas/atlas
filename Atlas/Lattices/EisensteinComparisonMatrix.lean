import Atlas.Lattices.EisensteinCrossData
import Atlas.Lattices.LeechForm

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra Matrix

abbrev EisensteinRealIndex := Fin 12 × Fin 2

def eisensteinRealCoordinates :
    EisensteinRationalCoordinates ≃ₗ[ℚ] (EisensteinRealIndex → ℚ) where
  toFun z p := if p.2 = 0 then (z p.1).re else (z p.1).im
  invFun x i := ⟨x (i,0), x (i,1)⟩
  left_inv z := by funext i; ext <;> simp
  right_inv x := by
    funext ⟨i,j⟩
    fin_cases j <;> simp
  map_add' z w := by funext p; split_ifs <;> simp_all
  map_smul' r z := by funext p; split_ifs <;> simp_all

def eisensteinCrossIndex (p : Omega) : Fin 24 :=
  ⟨8*p.1.1.val + 4*p.1.2.val + p.2.val, by
    have := p.1.1.isLt; have := p.1.2.isLt; have := p.2.isLt; omega⟩

def eisensteinComparisonMatrix : Matrix Omega EisensteinRealIndex ℚ := fun p q =>
  let v := eisensteinCrossVector (eisensteinCrossIndex p) q.1
  if q.2 = 0 then ((2*v.re-v.im : ℤ) : ℚ)/9 else ((-v.re+2*v.im : ℤ) : ℚ)/9

def eisensteinComparisonInverseMatrix : Matrix EisensteinRealIndex Omega ℚ := fun q p =>
  let v := eisensteinCrossVector (eisensteinCrossIndex p) q.1
  if q.2 = 0 then (v.re : ℚ)/8 else (v.im : ℚ)/8

def eisensteinRealGram : Matrix EisensteinRealIndex EisensteinRealIndex ℚ := fun p q =>
  if p.1 = q.1 then (if p.2 = q.2 then 2/9 else -1/9) else 0

theorem eisensteinComparison_matrix_inverse :
    eisensteinComparisonMatrix * eisensteinComparisonInverseMatrix = 1 := by
  decide +kernel

theorem eisensteinComparison_inverse_matrix :
    eisensteinComparisonInverseMatrix * eisensteinComparisonMatrix = 1 := by
  decide +kernel

theorem eisensteinComparison_matrix_gram :
    eisensteinComparisonMatrix.transpose * eisensteinComparisonMatrix =
      (8 : ℚ) • eisensteinRealGram := by
  decide +kernel

end Atlas.Lattices
