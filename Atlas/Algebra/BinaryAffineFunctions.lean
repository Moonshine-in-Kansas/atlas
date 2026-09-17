import Atlas.Algebra.BinaryReedMullerDuality

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

def binaryFourLinearPart (c : Fin 4 → Bit) : BinaryFour →ₗ[Bit] Bit :=
  ∑ i, c i • LinearMap.proj i

theorem binaryFourLinearPart_apply (c v : Fin 4 → Bit) :
    binaryFourLinearPart c v = ∑ i, c i * v i := by
  simp [binaryFourLinearPart]

theorem binaryAffineEvaluation_formula (c : Fin 5 → Bit) (v : BinaryFour) :
    binaryAffineEvaluation c v = c 0+binaryFourLinearPart (fun i => c i.succ) v := by
  simp [binaryAffineEvaluation,binaryAffineMonomials,binaryFourLinearPart_apply,
    Fin.sum_univ_succ]

theorem binaryFour_linear_formula (l : BinaryFour →ₗ[Bit] Bit) (v : BinaryFour) :
    l v = v 0*l ![1,0,0,0]+v 1*l ![0,1,0,0]+v 2*l ![0,0,1,0]+v 3*l ![0,0,0,1] := by
  have h : v = v 0 • (![1,0,0,0] : BinaryFour)+v 1 • ![0,1,0,0]+
      v 2 • ![0,0,1,0]+v 3 • ![0,0,0,1] := by
    funext i
    fin_cases i <;> simp
  rw [h,map_add,map_add,map_add,map_smul,map_smul,map_smul,map_smul]
  simp

/-- The affine monomial code contains every affine function, with no restriction
on its linear part. -/
theorem binaryAffineCode_mem_iff (w : BinaryFourWord) : w ∈ binaryAffineCode ↔
    ∃ a : Bit, ∃ l : BinaryFour →ₗ[Bit] Bit, ∀ v, w v=a+l v := by
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨c 0,binaryFourLinearPart (fun i => c i.succ),binaryAffineEvaluation_formula c⟩
  · rintro ⟨a,l,hl⟩
    refine ⟨![a,l ![1,0,0,0],l ![0,1,0,0],l ![0,0,1,0],l ![0,0,0,1]],?_⟩
    funext v
    rw [hl,binaryFour_linear_formula l v]
    simp [binaryAffineEvaluation,binaryAffineMonomials,Fin.sum_univ_succ]
    ring

/-- The affine code is the literal degree-at-most-one subcode of the quadratic code. -/
theorem binaryAffineCode_le_quadratic : binaryAffineCode ≤ binaryQuadraticCode := by
  rintro w ⟨c,rfl⟩
  refine ⟨![c 0,c 1,c 2,c 3,c 4,0,0,0,0,0,0],?_⟩
  funext v
  simp [binaryQuadraticEvaluation,binaryQuadraticMonomials,binaryAffineEvaluation,
    binaryAffineMonomials,Fin.sum_univ_succ]

end Atlas.Algebra
