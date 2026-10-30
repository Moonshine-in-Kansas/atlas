import FamilyWork.FixedOrbitNormalForm
import FamilyWork.CompatiblePositiveLifts

/-! The full positive graph–Frobenius fixed subgroup of the actual simply
connected E6 construction, over every quadratic extension of finite fields.
The normal form is a set equivalence with twelve F and twelve K parameters.
No full twisted-group order, center or simplicity is asserted here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6

variable (K : Type*) [Field K]

theorem e6OrbitLiftFactor_compatible (i : Fin 36) (t : K) :
    e6OrbitLiftFactor K (e6CompatiblePositiveRootLift K) i t = e6CompatibleRootX K i t := by
  change e6CompatiblePositiveRootHom K (e6PositiveRootEquiv i) (Multiplicative.ofAdd t) = _
  rw [e6CompatiblePositiveRootHom_equiv]
  rfl

theorem e6OrbitLiftFactor_compatible_commute (i : Fin 36)
    (hi : positiveDiagram i ≠ i) (s t : K) :
    Commute (e6OrbitLiftFactor K (e6CompatiblePositiveRootLift K) i s)
      (e6OrbitLiftFactor K (e6CompatiblePositiveRootLift K) (positiveDiagram i) t) := by
  simpa only [e6OrbitLiftFactor_compatible, e6CompatibleRootX] using
    e6CompatibleRootHom_diagram_commute K i hi (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

variable (F : Type*) [Field F] [Finite F] [Finite K] [Algebra F K]

theorem e6OrbitLiftFactor_compatible_twist (i : Fin 36) (t : K) :
    companionTwist F K (e6OrbitLiftFactor K (e6CompatiblePositiveRootLift K) i t) =
      e6OrbitLiftFactor K (e6CompatiblePositiveRootLift K) (positiveDiagram i)
        (Atlas.FiniteQuadratic.conjugation F K t) := by
  simpa only [e6OrbitLiftFactor_compatible] using e6CompatibleRootX_twist K F i t

theorem compatiblePositiveProduct_fixed_iff (hdeg : Module.finrank F K = 2)
    (s : Fin 36 → K) :
    (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s).val ∈
        companionFixedSubgroup F K ↔
      ∀ i, s (positiveDiagram i) = Atlas.FiniteQuadratic.conjugation F K (s i) :=
  e6OrbitLiftProduct_fixed_iff F K (e6CompatiblePositiveRootLift K)
    (e6OrbitLiftFactor_compatible_twist K F) (e6OrbitLiftFactor_compatible_commute K) hdeg s

/-- All actual positive fixed points, with exactly twelve base-field and
twelve quadratic-field coordinates. This is not an additive group isomorphism. -/
def companionPositiveFixedParametersEquiv (hdeg : Module.finrank F K = 2) :
    PositiveDiagramParameters.Parameters F K ≃ companionPositiveFixedSubgroup F K :=
  (PositiveDiagramParameters.fixedFunctionsEquiv F K hdeg).symm.trans
    (e6FixedOrbitProductEquiv F K (e6CompatiblePositiveRootLift K)
      (e6OrbitLiftFactor_compatible_twist K F) (e6OrbitLiftFactor_compatible_commute K) hdeg)

theorem companionPositiveFixedParametersEquiv_val (hdeg : Module.finrank F K = 2)
    (p : PositiveDiagramParameters.Parameters F K) :
    (companionPositiveFixedParametersEquiv K F hdeg p).val =
      positiveOrbitProduct (e6CompatibleRootX K) (PositiveDiagramParameters.expand F K p) := by
  change (e6FixedOrbitProduct F K (e6CompatiblePositiveRootLift K)
    (e6OrbitLiftFactor_compatible_twist K F) (e6OrbitLiftFactor_compatible_commute K) hdeg
    ((PositiveDiagramParameters.fixedFunctionsEquiv F K hdeg).symm p)).val = _
  rw [e6FixedOrbitProduct_val]
  change positiveOrbitProduct (e6OrbitLiftFactor K (e6CompatiblePositiveRootLift K))
    (PositiveDiagramParameters.expand F K p) = _
  congr 1
  funext i t
  exact e6OrbitLiftFactor_compatible K i t

/-- Uniform order of the full positive fixed subgroup, including q=2. -/
theorem companionPositiveFixedSubgroup_card (hdeg : Module.finrank F K = 2) :
    Nat.card (companionPositiveFixedSubgroup F K) = Nat.card F ^ 36 :=
  companionPositiveFixedSubgroup_card_of_compatible_lifts F K
    (e6CompatiblePositiveRootLift K) (e6OrbitLiftFactor_compatible_twist K F)
    (e6OrbitLiftFactor_compatible_commute K) hdeg

end Atlas.Chevalley.TwistedE6
