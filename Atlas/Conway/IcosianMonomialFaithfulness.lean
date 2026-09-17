import Atlas.Conway.IcosianMonomialEmbedding
import Atlas.Conway.IcosianMonomialKernel

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianMonomialRepresentation_injective :
    Function.Injective icosianMonomialRepresentation := by
  intro g h he
  have hp (i : Fin 3) : g.right.symm i=h.right.symm i := by
    by_contra hne
    have hv := congrArg (fun f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates =>
      f (Pi.single (g.right.symm i) (1 : IcosianQuaternion)) i) he
    have hz : (icosianMonomialUnits (g.left i) : IcosianQuaternion)=0 := by
      simpa [icosianMonomialRepresentation,icosianMonomialLinear,Pi.single_apply,Ne.symm hne] using hv
    exact (Units.ne_zero (icosianMonomialUnits (g.left i))) hz
  apply SemidirectProduct.ext
  · funext i
    apply icosianNormOne_value_injective
    have hv := congrArg (fun f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates =>
      f (Pi.single (g.right.symm i) (1 : IcosianQuaternion)) i) he
    simpa [icosianMonomialRepresentation,icosianMonomialLinear,icosianMonomialUnits,
      Pi.single_apply,← hp i] using hv
  · have hsymm : g.right.symm=h.right.symm := Equiv.ext hp
    simpa using congrArg Equiv.symm hsymm

theorem icosianMonomialToHermitian_injective : Function.Injective icosianMonomialToHermitian := by
  intro g h he
  apply Subtype.ext
  apply icosianMonomialRepresentation_injective
  exact congrArg Subtype.val he

theorem icosianMonomialToHermitian_range_card : Nat.card icosianMonomialToHermitian.range=2304 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective icosianMonomialToHermitian_injective).toEquiv]
  exact icosianLiftedMonomial_card

end Atlas.Conway
