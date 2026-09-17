import Atlas.Fischer.ReflectingRootProductReconstruction
import Atlas.Fischer.RootProductCentroid
import Atlas.Fischer.CoordinateHermitianSums

noncomputable section
namespace Atlas.Fischer

/-- The actual finite frame operator of any coordinate family. -/
def reflectingFrameOperator {J : Type*} [Fintype J] (r : J → Coordinates) :
    Module.End Scalar Coordinates := ∑ j, rootRankOne (r j)

theorem reflectingFrameOperator_apply {J : Type*} [Fintype J]
    (r : J → Coordinates) (x : Coordinates) :
    reflectingFrameOperator r x=∑ j, hermitian x (r j) • r j := by
  simp only [reflectingFrameOperator,LinearMap.sum_apply,rootRankOne_apply]

/-- The actual conjugate-bilinear finite root sum. -/
def reflectingMomentProduct {J : Type*} [Fintype J] (r : J → Coordinates) :
    Coordinates →ₛₗ[starRingEnd Scalar] Coordinates →ₛₗ[starRingEnd Scalar] Coordinates where
  toFun x :=
    { toFun := fun y => ∑ j, (hermitian (r j) x * hermitian (r j) y) • r j
      map_add' := by
        intro y z
        simp only [hermitian_add_right,mul_add,add_smul,Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        simp only [hermitian_smul_right,Finset.smul_sum,smul_smul,starRingEnd_apply]
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp only [LinearMap.add_apply,hermitian_add_right,add_mul,add_smul,Finset.sum_add_distrib]
    rfl
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    change (∑ j, (hermitian (r j) (a • x) * hermitian (r j) y) • r j)=
      star a • (∑ j, (hermitian (r j) x * hermitian (r j) y) • r j)
    simp only [LinearMap.smul_apply,hermitian_smul_right,Finset.smul_sum,smul_smul,starRingEnd_apply]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring

theorem reflectingMomentProduct_apply {J : Type*} [Fintype J]
    (r : J → Coordinates) (x y : Coordinates) :
    reflectingMomentProduct r x y=∑ j, (hermitian (r j) x * hermitian (r j) y) • r j := rfl

theorem reflectingMomentProduct_comm {J : Type*} [Fintype J]
    (r : J → Coordinates) (x y : Coordinates) :
    reflectingMomentProduct r x y=reflectingMomentProduct r y x := by
  simp only [reflectingMomentProduct_apply,mul_comm]

/-- The finite frame operator is self-adjoint for the retained linear-first form. -/
theorem reflectingFrameOperator_selfadjoint {J : Type*} [Fintype J]
    (r : J → Coordinates) (x y : Coordinates) :
    hermitian (reflectingFrameOperator r x) y=hermitian x (reflectingFrameOperator r y) := by
  simp only [reflectingFrameOperator_apply,hermitian_sum_left,hermitian_sum_right,
    hermitian_smul_left,hermitian_smul_right,hermitian_star]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The cubic finite moment is symmetric, directly from the finite sum. -/
theorem reflectingMomentProduct_cubic_swap {J : Type*} [Fintype J]
    (r : J → Coordinates) (x y z : Coordinates) :
    hermitian x (reflectingMomentProduct r y z)=hermitian y (reflectingMomentProduct r x z) := by
  simp only [reflectingMomentProduct_apply,hermitian_sum_right,hermitian_smul_right,
    star_mul,hermitian_star]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Only the diagonal norm contributes the correction72 to a root's moment. -/
theorem reflectingMomentProduct_diagonal {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i) (j : J) :
    reflectingMomentProduct r (r j) (r j)=reflectingFrameOperator r (r j)+(72 : Scalar) • r j := by
  classical
  have hh (i : J) : hermitian (r i) (r j)*hermitian (r i) (r j)=
      hermitian (r j) (r i)+(if i=j then (72 : Scalar) else 0) := by
    by_cases hi : i=j
    · subst i
      rw [(hr j).1.1]
      norm_num
    · have h := reflectingRoot_pairing_zero_or_mu3 (r i) (r j) (hr i) (hr j) (hd i j hi)
      have he : hermitian (r i) (r j)^2=star (hermitian (r i) (r j)) := by
        rcases h with h | ⟨a,ha⟩
        · simp [h]
        · rw [ha,mu3_conjugate]
      simpa only [pow_two,hermitian_star,if_neg hi,add_zero] using he
  simp only [reflectingMomentProduct_apply,hh,add_smul,Finset.sum_add_distrib,
    ← reflectingFrameOperator_apply]
  simp

end Atlas.Fischer
