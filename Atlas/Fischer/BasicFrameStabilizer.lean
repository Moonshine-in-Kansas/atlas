import Atlas.Fischer.SemilinearRayAction
import Atlas.Fischer.ParkerBasicFrame

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The full actual algebra stabilizer of the unordered24-basic-ray frame. -/
def basicFrameStabilizer : Subgroup SemilinearAlgebraAutomorphism where
  carrier := {e | ∃ σ : Equiv.Perm Omega, ∀ i,
    rootRay (e.val (basicAxis i))=rootRay (basicAxis (σ i))}
  one_mem' := ⟨1,fun _ => rfl⟩
  mul_mem' := by
    rintro e f ⟨σ,hσ⟩ ⟨τ,hτ⟩
    refine ⟨σ*τ,?_⟩
    intro i
    have h := congrArg (fun R : Finset Coordinates => R.map e.val.toEmbedding) (hτ i)
    rw [semilinearAlgebra_rootRay_map,semilinearAlgebra_rootRay_map,hσ] at h
    exact h
  inv_mem' := by
    rintro e ⟨σ,hσ⟩
    refine ⟨σ⁻¹,?_⟩
    intro i
    have h := congrArg (fun R : Finset Coordinates => R.map e.val.symm.toEmbedding) (hσ (σ.symm i))
    have hi : σ (σ.symm i)=i := σ.apply_symm_apply i
    rw [hi] at h
    change (rootRay (e.val (basicAxis (σ.symm i)))).map (e⁻¹).val.toEmbedding =
      (rootRay (basicAxis i)).map (e⁻¹).val.toEmbedding at h
    rw [semilinearAlgebra_rootRay_map,semilinearAlgebra_rootRay_map] at h
    change rootRay (e.val.symm (e.val (basicAxis (σ.symm i)))) =
      rootRay ((e⁻¹).val (basicAxis i)) at h
    rw [e.val.symm_apply_apply] at h
    exact h.symm

/-- Every retained scalar/Parker product lies in the full frame stabilizer. -/
theorem scalar_parker_mem_basicFrameStabilizer (a : Mu3) (h : ParkerStandardGroup) :
    scalarAlgebraRepresentation a * parkerAlgebraRepresentation h ∈ basicFrameStabilizer :=
  ⟨(parkerStandardProjection h).val,scalar_parker_basic_frame a h⟩

end Atlas.Fischer
