import Atlas.LinearGroups.SuzukiFamily.ProjectiveAction

/-! Root translations on the actual projective ovoid. -/
noncomputable section
namespace Atlas.SuzukiFamily
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem root_affine_vector (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b c d : F) :
    u m a b *ᵥ affineVector m c d =
      affineVector m (a+c) (b+d+a*theta F m c) := by
  have he := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => fun i => A i 0)
    (u_mul m hcard a b c d)
  ext i
  have hi := congrFun he i
  fin_cases i <;> simpa [Matrix.mul_apply,Matrix.mulVec,dotProduct,u,affineVector,Fin.sum_univ_succ] using hi

theorem root_infinity_vector (m : ℕ) (a b : F) :
    u m a b *ᵥ (infinityVector : Vector F)=infinityVector := by
  ext i
  fin_cases i <;> simp [u,infinityVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem root_affine (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b c d : F) :
    pointLeft (rootElement m a b) (affinePoint m c d) =
      affinePoint m (a+c) (b+d+a*theta F m c) := by
  change Projectivization.mk F (matrix (rootElement m a b) *ᵥ affineVector m c d) _ = _
  simp only [matrix_root,root_affine_vector m hcard]
  rfl

theorem root_infinity (m : ℕ) (a b : F) :
    pointLeft (rootElement m a b) infinityPoint = infinityPoint := by
  change Projectivization.mk F (matrix (rootElement m a b) *ᵥ infinityVector) _ = _
  simp only [matrix_root,root_infinity_vector]
  rfl
end Atlas.SuzukiFamily
