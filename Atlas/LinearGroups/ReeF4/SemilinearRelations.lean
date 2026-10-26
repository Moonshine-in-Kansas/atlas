import Atlas.LinearGroups.ReeF4.SemilinearSpanning

/-! A precise existence criterion for semilinear values on the entire star domain. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]
variable {R : Type*} [CommRing R] (σ : F →+* R)
variable {M : Type*} [AddCommGroup M] [Module R M]

def CompatibleSpanningValues (v : ExteriorIndex → M) : Prop :=
  ∀ a b : ExteriorIndex → F,
    (∑ i, a i • starSpanning (F := F) i) = (∑ i, b i • starSpanning (F := F) i) →
      (∑ i, σ (a i) • v i) = (∑ i, σ (b i) • v i)

theorem compatibleSpanningValues_of_map (f : StarCarrier (F := F) →ₛₗ[σ] M) :
    CompatibleSpanningValues σ (fun i => f (starSpanning i)) := by
  intro a b h
  have hh := congrArg f h
  simpa only [_root_.map_sum, LinearMap.map_smulₛₗ] using hh

theorem fromSpanningValues_apply (v : ExteriorIndex → M)
    (hv : CompatibleSpanningValues σ v) (j : ExteriorIndex) :
    fromSpanningValues σ v (starSpanning (F := F) j) = v j := by
  classical
  have h := hv (fun i => markedExteriorBasis.repr (starSpanning (F := F) j).val i)
    (Pi.single j 1) (by simpa using starSpanning_sum (starSpanning (F := F) j))
  simpa [fromSpanningValues, Pi.single_apply] using h

theorem exists_semilinear_iff_compatible (v : ExteriorIndex → M) :
    (∃ f : StarCarrier (F := F) →ₛₗ[σ] M, ∀ i, f (starSpanning i) = v i) ↔
      CompatibleSpanningValues σ v := by
  constructor
  · rintro ⟨f, hf⟩
    have h := compatibleSpanningValues_of_map σ f
    simpa only [hf] using h
  · intro hv
    exact ⟨fromSpanningValues σ v, fromSpanningValues_apply σ v hv⟩

end Atlas.ReeF4
