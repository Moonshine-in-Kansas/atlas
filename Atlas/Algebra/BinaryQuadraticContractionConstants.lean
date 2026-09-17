import Atlas.Algebra.BinaryQuadraticNormalization

noncomputable section
namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

theorem binaryQuadraticWord_affine_sum (w : binaryQuadraticCode)
    (a : Bit) (l : BinaryFour →ₗ[Bit] Bit) :
    (∑ v : BinaryFour, w.val v * (a+l v))=0 := by
  have hw : w.val ∈ binaryDot.orthogonal binaryAffineCode := by
    rw [← binaryQuadraticCode_eq_affine_orthogonal]
    exact w.property
  have ha : (fun v : BinaryFour => a+l v) ∈ binaryAffineCode :=
    (binaryAffineCode_mem_iff _).mpr ⟨a,l,fun _ => rfl⟩
  have h := hw _ ha
  rw [binaryDot_symmetric] at h
  exact h

/-- Constant parts of affine factors do not change a quadratic-word contraction. -/
theorem binaryQuadraticWord_contraction_constants (w : binaryQuadraticCode)
    (a b : Bit) (l m : BinaryFour →ₗ[Bit] Bit) :
    (∑ v : BinaryFour, w.val v * (l v+a) * (m v+b)) =
      ∑ v : BinaryFour, w.val v * l v * m v := by
  have h0 : (∑ v : BinaryFour, w.val v)=0 := by
    simpa using binaryQuadraticWord_affine_sum w 1 0
  have hl : (∑ v : BinaryFour, w.val v*l v)=0 := by
    simpa using binaryQuadraticWord_affine_sum w 0 l
  have hm : (∑ v : BinaryFour, w.val v*m v)=0 := by
    simpa using binaryQuadraticWord_affine_sum w 0 m
  have he (v : BinaryFour) : w.val v*(l v+a)*(m v+b)=
      w.val v*l v*m v+b*(w.val v*l v)+a*(w.val v*m v)+(a*b)*w.val v := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib,
    ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hl,hm,h0]
  ring

end Atlas.Algebra
