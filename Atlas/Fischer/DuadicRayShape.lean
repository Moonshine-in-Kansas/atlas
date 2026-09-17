import Atlas.Fischer.RootAxisInvariant

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Different duads give different rays whenever the actual product point
coordinates have the source's U_p/8 shape. -/
theorem duadic_shape_ray_implies_duad_eq (p q : Finset Omega)
    (hp : p.card = 2) (hq : q.card = 2) (r s : Coordinates)
    (hr : ∀ i, r (.inl i) = if i ∈ p then (-7 / 8 : Scalar) else 1 / 8)
    (hs : ∀ i, s (.inl i) = if i ∈ q then (-7 / 8 : Scalar) else 1 / 8)
    (h : rootRay r = rootRay s) : p = q := by
  classical
  have hv := rootRay_eq_of_axisSum s r
    (by rw [rootAxisSum_duadic_shape p hp r hr, rootAxisSum_duadic_shape q hq s hs])
    (by rw [rootAxisSum_duadic_shape q hq s hs]; norm_num) h
  apply Finset.ext
  intro i
  have he := congrFun hv (.inl i)
  rw [hr, hs] at he
  by_cases hi : i ∈ p <;> by_cases hj : i ∈ q <;> simp_all <;> norm_num at he

theorem basic_duadic_shape_rays_ne (i : Omega) (p : Finset Omega) (hp : p.card = 2)
    (r : Coordinates)
    (hr : ∀ j, r (.inl j) = if j ∈ p then (-7 / 8 : Scalar) else 1 / 8) :
    rootRay (basicAxis i) ≠ rootRay r := by
  intro h
  have hc := rootAxisSum_cube_of_ray_eq _ _ h
  rw [rootAxisSum_basic, rootAxisSum_duadic_shape p hp r hr] at hc
  norm_num at hc

theorem octadic_duadic_shape_rays_ne {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) (p : Finset Omega) (hp : p.card = 2) (r : Coordinates)
    (hr : ∀ j, r (.inl j) = if j ∈ p then (-7 / 8 : Scalar) else 1 / 8) :
    rootRay (octadicRoot Q χ) ≠ rootRay r := by
  intro h
  have hc := rootAxisSum_cube_of_ray_eq _ _ h
  rw [rootAxisSum_octadic, rootAxisSum_duadic_shape p hp r hr] at hc
  norm_num at hc

end Atlas.Fischer
