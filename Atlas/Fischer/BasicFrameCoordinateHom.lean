import Atlas.Fischer.BasicFrameScalarParker
import Atlas.Fischer.BasicOctadicRays

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Coordinate permutation recovered from the unique retained scalar/Parker
factorization of a full standard-frame stabilizer. -/
def basicFrameCoordinate (e : basicFrameStabilizer) : Mathieu24CodeModel :=
  parkerStandardProjection (basicFrameScalarParkerEquiv.symm e).2

theorem basicFrameCoordinate_ray (e : basicFrameStabilizer) (i : Omega) :
    rootRay (e.val.val (basicAxis i))=rootRay (basicAxis ((basicFrameCoordinate e).val i)) := by
  have he := congrArg Subtype.val (basicFrameScalarParkerEquiv.apply_symm_apply e)
  change scalarAlgebraRepresentation (basicFrameScalarParkerEquiv.symm e).1 *
    parkerAlgebraRepresentation (basicFrameScalarParkerEquiv.symm e).2=e.val at he
  rw [← he]
  exact scalar_parker_basic_frame _ _ i

/-- The induced map is characterized by its literal action on basic rays. -/
theorem basicFrameCoordinate_eq_of_ray (e : basicFrameStabilizer) (g : Mathieu24CodeModel)
    (h : ∀ i, rootRay (e.val.val (basicAxis i))=rootRay (basicAxis (g.val i))) :
    basicFrameCoordinate e=g := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  exact basicAxis_ray_injective ((basicFrameCoordinate_ray e i).symm.trans (h i))

def basicFrameCoordinateHom : basicFrameStabilizer →* Mathieu24CodeModel where
  toFun := basicFrameCoordinate
  map_one' := basicFrameCoordinate_eq_of_ray 1 1 (fun _ => rfl)
  map_mul' e f := by
    apply basicFrameCoordinate_eq_of_ray
    intro i
    have h := congrArg (fun R : Finset Coordinates => R.map e.val.val.toEmbedding)
      (basicFrameCoordinate_ray f i)
    rw [semilinearAlgebra_rootRay_map,semilinearAlgebra_rootRay_map,basicFrameCoordinate_ray] at h
    exact h

theorem basicFrameCoordinateHom_scalar_parker (a : Mu3) (h : ParkerStandardGroup) :
    basicFrameCoordinateHom ⟨scalarAlgebraRepresentation a * parkerAlgebraRepresentation h,
      scalar_parker_mem_basicFrameStabilizer a h⟩=parkerStandardProjection h :=
  basicFrameCoordinate_eq_of_ray _ _ (scalar_parker_basic_frame a h)

theorem basicFrameCoordinateHom_surjective : Function.Surjective basicFrameCoordinateHom := by
  intro g
  obtain ⟨h,hh⟩ := parkerStandardProjection_surjective g
  exact ⟨⟨scalarAlgebraRepresentation 1 * parkerAlgebraRepresentation h,
    scalar_parker_mem_basicFrameStabilizer 1 h⟩,
    (basicFrameCoordinateHom_scalar_parker 1 h).trans hh⟩

end Atlas.Fischer
