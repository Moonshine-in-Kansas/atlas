import Atlas.Fischer.ReflectingRootMomentInterpolation

noncomputable section
namespace Atlas.Fischer

/-- The exact frame trace for any finite normalized root family. -/
theorem reflectingFrameOperator_trace {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsRoot (r j)) :
    LinearMap.trace Scalar Coordinates (reflectingFrameOperator r)=9*(Fintype.card J : Scalar) := by
  have hn (j : J) : hermitian (r j) (r j)=9 := (hr j).1
  simp only [reflectingFrameOperator,map_sum,rootRankOne_trace,hn,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  ring

/-- The frame scalar is forced by one reflecting root and the actual dimension
and cardinality; no irreducibility or moment assumption is used. -/
theorem reflectingFrameOperator_eq_3528 {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (x : Coordinates) :
    reflectingFrameOperator r x=(3528 : Scalar) • x := by
  classical
  have hJ : Nonempty J := Fintype.card_pos_iff.mp (by rw [hc]; norm_num)
  let j : J := Classical.choice hJ
  obtain ⟨a,ha,hS⟩ := productCentroid_scalar (reflectingFrameOperator r)
    (reflectingFrameOperator_centroid r hr hd hc) (r j) (hr j).1 (hr j).2.1
  have hmap : reflectingFrameOperator r=a • (1 : Module.End Scalar Coordinates) := by
    apply LinearMap.ext
    exact hS
  have ht := congrArg (LinearMap.trace Scalar Coordinates) hmap
  rw [reflectingFrameOperator_trace r (fun j => (hr j).1),map_smul,LinearMap.trace_one,
    coordinates_dimension,hc] at ht
  norm_num at ht
  have he : a=3528 := by linear_combination -ht / 783
  rw [hS,he]

/-- The actual conjugate-bilinear product is recovered from its finite root sum. -/
theorem reflectingMomentProduct_eq_360 {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (x y : Coordinates) :
    reflectingMomentProduct r x y=(360 : Scalar) • product x y := by
  rw [reflectingMomentProduct_interpolation r hr hd hc,
    reflectingFrameOperator_eq_3528 r hr hd hc]
  module

/-- The second moment is3528 times the actual retained Hermitian form. -/
theorem reflectingRoot_second_moment {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (x y : Coordinates) :
    (∑ j, hermitian x (r j)*hermitian (r j) y)=3528*hermitian x y := by
  have h := congrArg (fun v => hermitian v y) (reflectingFrameOperator_eq_3528 r hr hd hc x)
  simpa only [reflectingFrameOperator_apply,hermitian_sum_left,hermitian_smul_left] using h

/-- The third moment is360 times the retained symmetric cubic. -/
theorem reflectingRoot_third_moment {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (x y z : Coordinates) :
    (∑ j, hermitian x (r j)*hermitian y (r j)*hermitian z (r j))=360*cubic x y z := by
  have h := congrArg (hermitian x) (reflectingMomentProduct_eq_360 r hr hd hc y z)
  simp only [reflectingMomentProduct_apply,hermitian_sum_right,hermitian_smul_right,
    star_mul,hermitian_star] at h
  norm_num at h
  change _=360*hermitian x (product y z)
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The moment formula also proves that the reflecting representatives span. -/
theorem reflectingRoot_span_top {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) : Submodule.span Scalar (Set.range r)=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hs : reflectingFrameOperator r x ∈ Submodule.span Scalar (Set.range r) := by
    rw [reflectingFrameOperator_apply]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  rw [reflectingFrameOperator_eq_3528 r hr hd hc] at hs
  exact (Submodule.smul_mem_iff _ (by norm_num : (3528 : Scalar) ≠ 0)).mp hs

/-- The literal finite root-sum reconstruction of the actual product. -/
theorem reflectingRoot_product_reconstruction {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hd : ∀ i j, i ≠ j → ¬ ∃ a : Mu3, r j=(a.val.val : Scalar) • r i)
    (hc : Fintype.card J=306936) (x y : Coordinates) :
    product x y=(1 / 360 : Scalar) •
      (∑ j, (hermitian (r j) x * hermitian (r j) y) • r j) := by
  change product x y=(1 / 360 : Scalar) • reflectingMomentProduct r x y
  rw [reflectingMomentProduct_eq_360 r hr hd hc,smul_smul]
  norm_num

end Atlas.Fischer
