import Atlas.Fischer.PointwiseAxisOctadSigns
import Atlas.Fischer.ReflectingRayFamily

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Fixed point axes recover the point coordinates through the intrinsic metric. -/
theorem pointwiseAxis_point_coordinate (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (x : Coordinates) (i : Omega) :
    e.val x (.inl i)=scalarParityAut (semilinearAlgebraParity e) (x (.inl i)) := by
  have h := semilinearAlgebraAutomorphism_hermitian e (u i) x
  rw [he] at h
  change hermitian (coordinateVector (.inl i)) _ = scalarParityAut _
    (hermitian (coordinateVector (.inl i)) _) at h
  rw [hermitian_coordinateVector_left,hermitian_coordinateVector_left] at h
  norm_num [coordinateWeight,map_mul,map_div,map_ofNat,scalarParityAut_star] at h
  exact h

/-- Every actual pointwise axis stabilizer preserves each duadic vector fibre,
with no residual cubic phase. -/
theorem pointwiseAxis_duadic_fibre (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    ∃ η : Module.Dual Bit (duadShortenedCode p.val),
      e.val (chosenDuadicRoot p ξ)=chosenDuadicRoot p η := by
  classical
  let x := e.val (chosenDuadicRoot p ξ)
  have hx (i : Omega) : x (.inl i)=if i ∈ p.val then (-7/8 : Scalar) else 1/8 := by
    dsimp [x]
    rw [pointwiseAxis_point_coordinate e he,chosenDuadicRoot_axis_coefficient]
    split_ifs <;> norm_num [map_div,map_ofNat]
  have hr : IsReflectingRoot x := semilinearAlgebra_isReflectingRoot e _
    (reflectingRootParameter_isReflectingRoot (.inr (.inr ⟨p,ξ⟩)))
  obtain ⟨t,ht⟩ := reflectingRootParameter_exhaust x hr
  rcases t with i | (⟨O,χ⟩ | ⟨q,η⟩)
  · exact False.elim (basic_duadic_shape_rays_ne i p.val p.property x hx ht.symm)
  · exact False.elim (octadic_duadic_shape_rays_ne (chosenOctadCalibration O) χ p.val p.property x hx ht.symm)
  · have hpq : p=q := Subtype.ext (duadic_shape_ray_implies_duad_eq p.val q.val p.property q.property
        x (chosenDuadicRoot q η) hx (chosenDuadicRoot_axis_coefficient q η) ht)
    subst q
    refine ⟨η,?_⟩
    exact rootRay_eq_of_axisSum _ _
      ((rootAxisSum_duadic_shape p.val p.property x hx).trans (chosenDuadicRoot_axisSum p η).symm)
      (by rw [chosenDuadicRoot_axisSum]; norm_num) ht

/-- Cocode transitivity supplies an actual adjustment fixing a prescribed
duadic root, after an arbitrary pointwise axis stabilizer has acted. -/
theorem pointwiseAxis_duadic_adjustment (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    ∃ d : Cocode, parkerCoordinateAction (parkerCocodeStandard d)
      (e.val (chosenDuadicRoot p ξ))=chosenDuadicRoot p ξ := by
  obtain ⟨η,hη⟩ := pointwiseAxis_duadic_fibre e he p ξ
  rw [hη]
  exact duadCharacterProduct_transitive p.val p.property
    (duadChosenOctadPair p.val p.property).1 (duadChosenOctadPair p.val p.property).2
    (duadChosenOctadPair_intersection p.val p.property)
    (chosenOctadCalibration _) (chosenOctadCalibration _) η ξ

end Atlas.Fischer
