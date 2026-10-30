import FamilyWork.WitnessedPositiveProduct
import FamilyWork.OrbitProductEquivariance
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionPositiveOrder

/-! The actual E6 positive subgroup in the diagram-orbit order, for any
explicit choice of root lifts. This is a set normal form with exact factors;
the twist-compatible choice is supplied separately. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6

variable (K : Type*) [Field K]

def e6PositiveParameterEquiv : (Fin 36 → K) ≃
    ({β : E6Data.Root // E6Data.base.IsPos β} → K) where
  toFun s β := s (e6PositiveRootEquiv.symm β)
  invFun t i := t (e6PositiveRootEquiv i)
  left_inv s := by funext i; simp
  right_inv t := by funext β; simp

variable (L : ∀ β : {β : E6Data.Root // E6Data.base.IsPos β},
  WeightCompanionRootLift (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K β.val)

def e6OrbitLiftFactor (i : Fin 36) (t : K) : SelectedWeightCompanion .E6 K :=
  weightCompanionRootLiftHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K (L (e6PositiveRootEquiv i))
    (Multiplicative.ofAdd t)

def e6OrbitLiftProduct (s : Fin 36 → K) :
    selectedWeightCompanionPositiveSubgroup .E6 K :=
  positiveRootWitnessedProduct (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K L e6PositiveRootOrbitOrder
    (e6PositiveParameterEquiv K s)

theorem e6OrbitLiftProduct_val (s : Fin 36 → K) :
    (e6OrbitLiftProduct K L s).val = positiveOrbitProduct (e6OrbitLiftFactor K L) s := by
  change ((e6PositiveOrbitOrder.map e6PositiveRootEnumeration).map fun β =>
      weightCompanionRootLiftHom (rootDatum .E6).pairing (rootDatum .E6).base
        (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
        (selectedWeightOrbits_minuscule .E6) K (L β)
        (Multiplicative.ofAdd (s (e6PositiveRootEquiv.symm β)))).prod = _
  rw [List.map_map]
  unfold positiveOrbitProduct
  congr 1
  apply List.map_congr_left
  intro i _
  change weightCompanionRootLiftHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K (L (e6PositiveRootEquiv i))
    (Multiplicative.ofAdd (s (e6PositiveRootEquiv.symm (e6PositiveRootEquiv i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

def e6OrbitLiftProductEquiv :
    (Fin 36 → K) ≃ selectedWeightCompanionPositiveSubgroup .E6 K :=
  (e6PositiveParameterEquiv K).trans
    (positiveRootWitnessedProductEquiv (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K L e6PositiveRootOrbitOrder
      e6PositiveRootOrbitOrder_nodup e6PositiveRootOrbitOrder_pairwise_height
      mem_e6PositiveRootOrbitOrder E6Data.simpleDiamondProducts)

@[simp] theorem e6OrbitLiftProductEquiv_apply (s : Fin 36 → K) :
    e6OrbitLiftProductEquiv K L s = e6OrbitLiftProduct K L s := rfl

theorem e6OrbitLiftProduct_injective : Function.Injective (e6OrbitLiftProduct K L) :=
  (e6OrbitLiftProductEquiv K L).injective

theorem e6OrbitLiftProduct_surjective : Function.Surjective (e6OrbitLiftProduct K L) :=
  (e6OrbitLiftProductEquiv K L).surjective

end Atlas.Chevalley.TwistedE6
