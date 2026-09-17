import Atlas.Fischer.BasicFrameStabilizer
import Atlas.Fischer.BasicFrameNormalization
import Atlas.Fischer.AxisPermutationParkerFactor
import Atlas.Fischer.ScalarParkerUniqueness

noncomputable section
namespace Atlas.Fischer

/-- The full actual frame stabilizer consists exactly of cubic scalars times
the retained Parker group. This does not presume generated-group containment. -/
theorem mem_basicFrameStabilizer_iff_scalar_parker (e : SemilinearAlgebraAutomorphism) :
    e ∈ basicFrameStabilizer ↔ ∃ a : Mu3, ∃ h : ParkerStandardGroup,
      e=scalarAlgebraRepresentation a * parkerAlgebraRepresentation h := by
  constructor
  · rintro ⟨σ,hσ⟩
    obtain ⟨a,g,hg,hu⟩ := basicFrame_scalar_golay e σ hσ
    obtain ⟨h,hh⟩ := axisPermutation_scalar_parker_factor e a g hu
    exact ⟨a,h,hh⟩
  · rintro ⟨a,h,rfl⟩
    exact scalar_parker_mem_basicFrameStabilizer a h

/-- The unique scalar/Parker coordinates of the actual full frame stabilizer. -/
def basicFrameScalarParkerEquiv : Mu3 × ParkerStandardGroup ≃ basicFrameStabilizer :=
  Equiv.ofBijective
    (fun t => ⟨scalarAlgebraRepresentation t.1 * parkerAlgebraRepresentation t.2,
      scalar_parker_mem_basicFrameStabilizer t.1 t.2⟩)
    ⟨fun x y h => scalar_parker_factor_injective (congrArg Subtype.val h),by
      intro e
      obtain ⟨a,h,hh⟩ := (mem_basicFrameStabilizer_iff_scalar_parker e.val).mp e.property
      exact ⟨(a,h),Subtype.ext hh.symm⟩⟩

/-- Exact full frame-stabilizer order, from its proved scalar/Parker coordinates. -/
theorem basicFrameStabilizer_order : Nat.card basicFrameStabilizer = 3008385515520 := by
  rw [← Nat.card_congr basicFrameScalarParkerEquiv,Nat.card_prod,mu3_card,
    parkerStandardGroup_order_value]

end Atlas.Fischer
