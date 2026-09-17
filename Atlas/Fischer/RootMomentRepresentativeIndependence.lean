import Atlas.Fischer.ReflectingRootAutomaticMoments

noncomputable section
namespace Atlas.Fischer

/-- The frame operator is unchanged by independently chosen cubic phases. -/
theorem reflectingFrameOperator_phases {J : Type*} [Fintype J]
    (r : J → Coordinates) (a : J → Mu3) :
    reflectingFrameOperator (fun j => (a j).val.val • r j)=reflectingFrameOperator r := by
  apply LinearMap.ext
  intro x
  simp only [reflectingFrameOperator_apply,hermitian_smul_right,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h := cube_root_unit_norm ((mem_rootsOfUnity' _ _).mp (a j).property)
  linear_combination hermitian x (r j)*h

/-- The cubic root sum is unchanged by independently chosen cubic phases. -/
theorem reflectingMomentProduct_phases {J : Type*} [Fintype J]
    (r : J → Coordinates) (a : J → Mu3) :
    reflectingMomentProduct (fun j => (a j).val.val • r j)=reflectingMomentProduct r := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [reflectingMomentProduct_apply,hermitian_smul_left,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h := (mem_rootsOfUnity' _ _).mp (a j).property
  linear_combination (hermitian (r j) x*hermitian (r j) y)*h

theorem reflectingRoot_second_moment_phases {J : Type*} [Fintype J]
    (r : J → Coordinates) (a : J → Mu3) (x y : Coordinates) :
    (∑ j, hermitian x ((a j).val.val • r j)*hermitian ((a j).val.val • r j) y)=
      ∑ j, hermitian x (r j)*hermitian (r j) y := by
  have h := congrArg (fun S : Module.End Scalar Coordinates => hermitian (S x) y)
    (reflectingFrameOperator_phases r a)
  simpa only [reflectingFrameOperator_apply,hermitian_sum_left,hermitian_smul_left] using h

theorem reflectingRoot_third_moment_phases {J : Type*} [Fintype J]
    (r : J → Coordinates) (a : J → Mu3) (x y z : Coordinates) :
    (∑ j, hermitian x ((a j).val.val • r j)*hermitian y ((a j).val.val • r j)*
      hermitian z ((a j).val.val • r j))=
      ∑ j, hermitian x (r j)*hermitian y (r j)*hermitian z (r j) := by
  simp only [hermitian_smul_right]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg star ((mem_rootsOfUnity' _ _).mp (a j).property)
  simp only [star_pow,star_one] at h
  linear_combination (hermitian x (r j)*hermitian y (r j)*hermitian z (r j))*h

theorem reflectingFrameOperator_reindex {J K : Type*} [Fintype J] [Fintype K]
    (r : J → Coordinates) (e : K ≃ J) :
    reflectingFrameOperator (r ∘ e)=reflectingFrameOperator r :=
  Equiv.sum_comp e (fun j => rootRankOne (r j))

theorem reflectingMomentProduct_reindex {J K : Type*} [Fintype J] [Fintype K]
    (r : J → Coordinates) (e : K ≃ J) :
    reflectingMomentProduct (r ∘ e)=reflectingMomentProduct r := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact Equiv.sum_comp e (fun j => (hermitian (r j) x*hermitian (r j) y) • r j)

end Atlas.Fischer
