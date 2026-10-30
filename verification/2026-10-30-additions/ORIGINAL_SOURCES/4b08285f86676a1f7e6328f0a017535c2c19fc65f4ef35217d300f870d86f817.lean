import FamilyWork.OrbitNormalForm
import FamilyWork.FixedParameters
import Atlas.LinearGroups.Chevalley.TwistedE6.CompanionTwist

/-! Restrict the actual positive normal form to graph–field fixed points.
The compatible-lift hypotheses are explicit here and discharged by the
specific folded-root lift family in the final application. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The full positive fixed subgroup in the actual simply connected model. -/
def companionPositiveFixedSubgroup : Subgroup (SelectedWeightCompanion .E6 K) :=
  selectedWeightCompanionPositiveSubgroup .E6 K ⊓ companionFixedSubgroup F K

variable (L : ∀ β : {β : E6Data.Root // E6Data.base.IsPos β},
  WeightCompanionRootLift (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K β.val)
  (htwist : ∀ i t, companionTwist F K (e6OrbitLiftFactor K L i t) =
    e6OrbitLiftFactor K L (positiveDiagram i) (Atlas.FiniteQuadratic.conjugation F K t))
  (hcomm : ∀ i, positiveDiagram i ≠ i → ∀ s t,
    Commute (e6OrbitLiftFactor K L i s) (e6OrbitLiftFactor K L (positiveDiagram i) t))

theorem e6OrbitLiftFactor_product_injective :
    Function.Injective (positiveOrbitProduct (e6OrbitLiftFactor K L)) := by
  intro s t h
  apply e6OrbitLiftProduct_injective K L
  apply Subtype.ext
  simpa only [e6OrbitLiftProduct_val] using h

include htwist hcomm

theorem e6OrbitLiftProduct_fixed_iff (hdeg : Module.finrank F K = 2)
    (s : Fin 36 → K) :
    (e6OrbitLiftProduct K L s).val ∈ companionFixedSubgroup F K ↔
      ∀ i, s (positiveDiagram i) = Atlas.FiniteQuadratic.conjugation F K (s i) := by
  change companionTwist F K (e6OrbitLiftProduct K L s).val =
    (e6OrbitLiftProduct K L s).val ↔ _
  rw [e6OrbitLiftProduct_val]
  exact positiveOrbitProduct_fixed_iff (e6OrbitLiftFactor K L)
    (companionTwist F K).toMonoidHom (Atlas.FiniteQuadratic.conjugation F K)
    htwist hcomm (e6OrbitLiftFactor_product_injective K L)
    (Atlas.FiniteQuadratic.conjugation_conjugation hdeg) s

def e6FixedOrbitProduct (hdeg : Module.finrank F K = 2)
    (s : PositiveDiagramParameters.FixedFunctions F K) : companionPositiveFixedSubgroup F K :=
  ⟨(e6OrbitLiftProduct K L s.val).val, ⟨(e6OrbitLiftProduct K L s.val).property,
    (e6OrbitLiftProduct_fixed_iff F K L htwist hcomm hdeg s.val).mpr s.property⟩⟩

theorem e6FixedOrbitProduct_val (hdeg : Module.finrank F K = 2)
    (s : PositiveDiagramParameters.FixedFunctions F K) :
    (e6FixedOrbitProduct F K L htwist hcomm hdeg s).val =
      positiveOrbitProduct (e6OrbitLiftFactor K L) s.val :=
  e6OrbitLiftProduct_val K L s.val

theorem e6FixedOrbitProduct_injective (hdeg : Module.finrank F K = 2) :
    Function.Injective (e6FixedOrbitProduct F K L htwist hcomm hdeg) := by
  intro s t h
  apply Subtype.ext
  apply e6OrbitLiftFactor_product_injective K L
  simpa only [e6FixedOrbitProduct_val] using congrArg Subtype.val h

theorem e6FixedOrbitProduct_surjective (hdeg : Module.finrank F K = 2) :
    Function.Surjective (e6FixedOrbitProduct F K L htwist hcomm hdeg) := by
  intro g
  obtain ⟨s, hs⟩ := e6OrbitLiftProduct_surjective K L ⟨g.val, g.property.1⟩
  have hval : (e6OrbitLiftProduct K L s).val = g.val := congrArg Subtype.val hs
  have hfixed : (e6OrbitLiftProduct K L s).val ∈ companionFixedSubgroup F K := by
    rw [hval]
    exact g.property.2
  refine ⟨⟨s, (e6OrbitLiftProduct_fixed_iff F K L htwist hcomm hdeg s).mp hfixed⟩, ?_⟩
  exact Subtype.ext hval

/-- A set equivalence, not a direct-product group decomposition. -/
def e6FixedOrbitProductEquiv (hdeg : Module.finrank F K = 2) :
    PositiveDiagramParameters.FixedFunctions F K ≃ companionPositiveFixedSubgroup F K :=
  Equiv.ofBijective (e6FixedOrbitProduct F K L htwist hcomm hdeg)
    ⟨e6FixedOrbitProduct_injective F K L htwist hcomm hdeg,
      e6FixedOrbitProduct_surjective F K L htwist hcomm hdeg⟩

theorem companionPositiveFixedSubgroup_card_of_compatible_lifts
    (hdeg : Module.finrank F K = 2) :
    Nat.card (companionPositiveFixedSubgroup F K) = Nat.card F ^ 36 := by
  calc
    _ = Nat.card (PositiveDiagramParameters.FixedFunctions F K) :=
      (Nat.card_congr (e6FixedOrbitProductEquiv F K L htwist hcomm hdeg)).symm
    _ = Nat.card F ^ 36 := PositiveDiagramParameters.fixedFunctions_card F K hdeg

end Atlas.Chevalley.TwistedE6
