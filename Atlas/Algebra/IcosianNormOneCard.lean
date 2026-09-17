import Atlas.Algebra.IcosianNormOneGroup
import Atlas.Algebra.IcosianNormOneExhaustion
import Atlas.Algebra.IcosianParityIntegral
import Atlas.Algebra.IcosianShortParity

noncomputable section
namespace Atlas.Algebra

/-- The scalar classification is a bijection with all actual norm-one integral quaternions. -/
def icosianNormOneCoordinatesEquiv :
    {v // v ∈ icosianNormOneCoordinates} ≃ icosianNormOneGroup :=
  Equiv.ofBijective (fun v => icosianNormOneGroupOf
    (icosianCoordinatesQuaternion v.val)
    (isIcosian_coordinates_of_parity v.val
      (icosianShortCoordinates_parity v.val (Finset.mem_filter.mp v.property).1))
    (icosianNormOneCoordinates_norm v.property)) (by
      constructor
      · intro v w h
        apply Subtype.ext
        apply icosianCoordinatesQuaternion_injective
        exact congrArg (fun u : icosianNormOneGroup => u.val.val) h
      · intro u
        obtain ⟨v,hv,he⟩ := icosianNormOne_exhaust u.property (icosianNormOneGroup_norm u)
        refine ⟨⟨v,hv⟩,?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact he)

instance icosianNormOneGroup_finite : Finite icosianNormOneGroup :=
  Finite.of_equiv _ icosianNormOneCoordinatesEquiv

theorem icosianNormOneGroup_card : Nat.card icosianNormOneGroup=120 := by
  rw [← Nat.card_congr icosianNormOneCoordinatesEquiv]
  simpa using icosianNormOneCoordinates_card

end Atlas.Algebra
