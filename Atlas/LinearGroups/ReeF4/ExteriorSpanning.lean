import Atlas.LinearGroups.ReeF4.ExteriorKernel

/-! A finite, complete spanning family for the actual star domain. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

/-- Use the finite coordinate enumeration to order the exterior basis. -/
def orderedMarkedBasis : Module.Basis (Fin (Fintype.card TraceZeroCoordinate)) F
    (TraceZero F) := markedBasis.reindex (Fintype.equivFin TraceZeroCoordinate)

abbrev ExteriorIndex := Set.powersetCard (Fin (Fintype.card TraceZeroCoordinate)) 2

def markedExteriorBasis : Module.Basis ExteriorIndex F (⋀[F]^2 (TraceZero F)) :=
  orderedMarkedBasis.exteriorPower 2

def starSpanning (s : ExteriorIndex) : StarCarrier (F := F) :=
  starProjection (markedExteriorBasis s)

theorem starSpanning_span :
    Submodule.span F (Set.range (starSpanning (F := F))) = ⊤ := by
  change Submodule.span F (Set.range (starProjection ∘ markedExteriorBasis)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq,
    Submodule.map_top, LinearMap.range_eq_top.mpr starProjection_surjective]

theorem exteriorIndex_card : Fintype.card ExteriorIndex = 325 := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card]
  norm_num [TraceZeroCoordinate]
  decide

/-- Coordinates in the exterior basis give a concrete decomposition in the domain. -/
theorem starSpanning_sum (x : StarCarrier (F := F)) :
    ∑ i : ExteriorIndex, (markedExteriorBasis.repr x.val) i • starSpanning i = x := by
  have h := congrArg (starProjection (F := F))
    ((markedExteriorBasis (F := F)).sum_repr x.val)
  simpa only [_root_.map_sum, _root_.map_smul, starProjection_of_mem, starSpanning] using h

/-- Agreement on the finite family implies equality on the complete domain. -/
theorem starSpanning_ext {M : Type*} [AddCommMonoid M] [Module F M]
    (f g : StarCarrier (F := F) →ₗ[F] M)
    (h : ∀ i, f (starSpanning i) = g (starSpanning i)) : f = g := by
  apply LinearMap.ext
  intro x
  rw [← starSpanning_sum x]
  simp only [map_sum, map_smul, h]

end Atlas.ReeF4
