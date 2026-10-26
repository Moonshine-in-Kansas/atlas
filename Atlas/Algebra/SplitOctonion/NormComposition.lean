import Atlas.Algebra.SplitOctonion.Basic

namespace Atlas.SplitOctonion
variable {F : Type*} [CommRing F]

theorem conjugate_conjugate (x : Carrier F) : conjugate (conjugate x)=x := by
  ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,conjugate,trace,unit] <;> ring

theorem conjugate_smul (r : F) (x : Carrier F) : conjugate (r • x)=r • conjugate x := by
  ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,conjugate,trace,unit] <;> ring

theorem norm_conjugate (x : Carrier F) : norm (conjugate x)=norm x := by
  simp [Matrix.vecHead,Matrix.vecTail,norm,conjugate,trace,unit]; ring

theorem norm_smul (r : F) (x : Carrier F) : norm (r • x)=r^2*norm x := by
  simp [Matrix.vecHead,Matrix.vecTail,norm]; ring

/-- A norm-composition identity; no associative octonion multiplication is assumed. -/
theorem mul_mul_conjugate (x y : Carrier F) : mul (mul x y) (conjugate y)=norm y • x := by
  ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,mul,conjugate,trace,norm,unit] <;> ring

theorem conjugate_mul_mul (x y : Carrier F) : mul (conjugate x) (mul x y)=norm x • y := by
  ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail,mul,conjugate,trace,norm,unit] <;> ring

theorem conjugate_mul_conjugate_product_left (x y : Carrier F) :
    conjugate (mul y (conjugate (mul x y)))=norm y • x := by
  rw [conjugate_mul_reverse,conjugate_conjugate,mul_mul_conjugate]

theorem conjugate_mul_conjugate_product_right (x y : Carrier F) :
    conjugate (mul (conjugate (mul x y)) x)=norm x • y := by
  rw [conjugate_mul_reverse,conjugate_conjugate,conjugate_mul_mul]

end Atlas.SplitOctonion
