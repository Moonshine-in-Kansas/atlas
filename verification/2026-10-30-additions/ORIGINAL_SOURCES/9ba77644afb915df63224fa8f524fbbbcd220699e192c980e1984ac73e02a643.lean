import FamilyWork.PositiveFixedOrder
import Atlas.LinearGroups.Chevalley.PositiveWitnessedAdjointInjective

/-! the adjoint projection on the inherited E6 positive subgroup.

Here U is exactly `selectedWeightCompanionPositiveSubgroup .E6 K`. Its adjoint
image is named as an image, without identifying it with a separately defined
adjoint positive subgroup. Injectivity on U is inherited from the existing
positive-product theorem. The compatible orbit normal form makes U stable
under graph--Frobenius, so an adjoint fixed point in this image has a unique
U lift, which is fixed.

No full-group projection injectivity is asserted. The fixed adjoint image
order is transferred along the actual restricted group isomorphism.
Verification receipts are recorded separately. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6

variable (K : Type*) [Field K]

/-- Reuse the existing positive-subgroup faithfulness theorem, specialized to E6. -/
theorem e6PositiveRho_injective :
    Function.Injective (fun u : selectedWeightCompanionPositiveSubgroup .E6 K =>
      selectedWeightCompanionRho .E6 K u.val) :=
  positiveWitnessedWeightCompanion_adjoint_injective
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K E6Data.simpleDiamondProducts

/-- The explicit orbit-order parameters can already be recovered after rho.
The lift family remains arbitrary and explicit. -/
theorem e6OrbitLiftProduct_rho_injective
    (L : ∀ β : {β : E6Data.Root // E6Data.base.IsPos β},
      WeightCompanionRootLift (rootDatum .E6).pairing (rootDatum .E6).base
        (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
        (selectedWeightOrbits_minuscule .E6) K β.val) :
    Function.Injective (fun s : Fin 36 → K =>
      selectedWeightCompanionRho .E6 K (e6OrbitLiftProduct K L s).val) := by
  intro s t h
  apply (e6PositiveParameterEquiv K).injective
  apply positiveRootLiftProduct_adjoint_injective
    (rootDatum .E6).pairing (rootDatum .E6).base K
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) L e6PositiveRootOrbitOrder
    e6PositiveRootOrbitOrder_nodup e6PositiveRootOrbitOrder_pairwise_height
    mem_e6PositiveRootOrbitOrder
  exact h

/-- Literal image of the inherited companion positive subgroup under rho. -/
def e6PositiveAdjointImage : Subgroup (Model .E6 K) :=
  (selectedWeightCompanionPositiveSubgroup .E6 K).map (selectedWeightCompanionRho .E6 K)

def e6PositiveProjection :
    selectedWeightCompanionPositiveSubgroup .E6 K →* e6PositiveAdjointImage K where
  toFun u := ⟨selectedWeightCompanionRho .E6 K u.val,
    Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (selectedWeightCompanionRho .E6 K))
  map_mul' u v := Subtype.ext (map_mul (selectedWeightCompanionRho .E6 K) u.val v.val)

@[simp] theorem e6PositiveProjection_val (u : selectedWeightCompanionPositiveSubgroup .E6 K) :
    (e6PositiveProjection K u).val = selectedWeightCompanionRho .E6 K u.val := rfl

theorem e6PositiveProjection_injective : Function.Injective (e6PositiveProjection K) := by
  intro u v h
  apply e6PositiveRho_injective K
  exact congrArg Subtype.val h

theorem e6PositiveProjection_surjective : Function.Surjective (e6PositiveProjection K) := by
  intro a
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp a.property
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

/-- Rho is a group isomorphism from the existing U to its literal image. -/
def e6PositiveProjectionEquiv :
    selectedWeightCompanionPositiveSubgroup .E6 K ≃* e6PositiveAdjointImage K :=
  MulEquiv.ofBijective (e6PositiveProjection K)
    ⟨e6PositiveProjection_injective K, e6PositiveProjection_surjective K⟩

@[simp] theorem e6PositiveProjectionEquiv_val
    (u : selectedWeightCompanionPositiveSubgroup .E6 K) :
    (e6PositiveProjectionEquiv K u).val = selectedWeightCompanionRho .E6 K u.val := rfl

variable (F : Type*) [Field F] [Finite F] [Finite K] [Algebra F K]

/-- Exact covariance of the compatible normal form, without a degree-two premise. -/
theorem e6OrbitLiftProduct_compatible_twist (s : Fin 36 → K) :
    companionTwist F K (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s).val =
      (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K)
        (fun i => Atlas.FiniteQuadratic.conjugation F K (s (positiveDiagram i)))).val := by
  rw [e6OrbitLiftProduct_val, e6OrbitLiftProduct_val]
  exact positiveOrbitProduct_twist (e6OrbitLiftFactor K (e6CompatiblePositiveRootLift K))
      (companionTwist F K).toMonoidHom (Atlas.FiniteQuadratic.conjugation F K)
      (e6OrbitLiftFactor_compatible_twist K F) (e6OrbitLiftFactor_compatible_commute K) s

/-- The actual graph--Frobenius map carries every element of U back into U. -/
theorem e6PositiveSubgroup_twist_mem (g : SelectedWeightCompanion .E6 K)
    (hg : g ∈ selectedWeightCompanionPositiveSubgroup .E6 K) :
    companionTwist F K g ∈ selectedWeightCompanionPositiveSubgroup .E6 K := by
  obtain ⟨s, hs⟩ := e6OrbitLiftProduct_surjective K (e6CompatiblePositiveRootLift K) ⟨g, hg⟩
  have hval : (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K) s).val = g :=
    congrArg Subtype.val hs
  rw [← hval, e6OrbitLiftProduct_compatible_twist K F]
  exact (e6OrbitLiftProduct K (e6CompatiblePositiveRootLift K)
    (fun i => Atlas.FiniteQuadratic.conjugation F K (s (positiveDiagram i)))).property

/-- A positive element is fixed exactly when its adjoint projection is fixed.
The converse uses injectivity only between two elements of U. -/
theorem e6PositiveSubgroup_fixed_iff_rho_fixed (g : SelectedWeightCompanion .E6 K)
    (hg : g ∈ selectedWeightCompanionPositiveSubgroup .E6 K) :
    g ∈ companionFixedSubgroup F K ↔
      selectedWeightCompanionRho .E6 K g ∈ adjointFixedSubgroup F K := by
  constructor
  · intro hfixed
    exact (companionFixedProjection F K ⟨g, hfixed⟩).property
  · intro hfixed
    have hadj : adjointTwist F K (selectedWeightCompanionRho .E6 K g) =
        selectedWeightCompanionRho .E6 K g := hfixed
    change companionTwist F K g = g
    have he :
        (⟨companionTwist F K g, e6PositiveSubgroup_twist_mem K F g hg⟩ :
          selectedWeightCompanionPositiveSubgroup .E6 K) = ⟨g, hg⟩ := by
      apply e6PositiveRho_injective K
      exact (companionTwist_rho F K g).trans hadj
    exact congrArg Subtype.val he

/-- The adjoint fixed points in the literal image of U. -/
def e6PositiveFixedAdjointImage : Subgroup (Model .E6 K) :=
  e6PositiveAdjointImage K ⊓ adjointFixedSubgroup F K

/-- Restrict the actual projection to the already defined positive fixed carrier. -/
def e6PositiveFixedProjection :
    companionPositiveFixedSubgroup F K →* e6PositiveFixedAdjointImage K F where
  toFun g := ⟨selectedWeightCompanionRho .E6 K g.val, by
    constructor
    · exact Subgroup.mem_map.mpr ⟨g.val, g.property.1, rfl⟩
    · exact (companionFixedProjection F K ⟨g.val, g.property.2⟩).property⟩
  map_one' := Subtype.ext (map_one (selectedWeightCompanionRho .E6 K))
  map_mul' g h := Subtype.ext (map_mul (selectedWeightCompanionRho .E6 K) g.val h.val)

@[simp] theorem e6PositiveFixedProjection_val (g : companionPositiveFixedSubgroup F K) :
    (e6PositiveFixedProjection K F g).val = selectedWeightCompanionRho .E6 K g.val := rfl

theorem e6PositiveFixedProjection_injective :
    Function.Injective (e6PositiveFixedProjection K F) := by
  intro g h heq
  apply Subtype.ext
  have hu : (⟨g.val, g.property.1⟩ : selectedWeightCompanionPositiveSubgroup .E6 K) =
      ⟨h.val, h.property.1⟩ := by
    apply e6PositiveRho_injective K
    exact congrArg Subtype.val heq
  exact congrArg (fun u : selectedWeightCompanionPositiveSubgroup .E6 K => u.val) hu

theorem e6PositiveFixedProjection_surjective :
    Function.Surjective (e6PositiveFixedProjection K F) := by
  intro a
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp a.property.1
  have hfixed : g ∈ companionFixedSubgroup F K := by
    apply (e6PositiveSubgroup_fixed_iff_rho_fixed K F g hg).mpr
    rw [he]
    exact a.property.2
  exact ⟨⟨g, ⟨hg, hfixed⟩⟩, Subtype.ext he⟩

/-- The inherited positive fixed subgroup is isomorphic to the fixed part of rho(U). -/
def e6PositiveFixedProjectionEquiv :
    companionPositiveFixedSubgroup F K ≃* e6PositiveFixedAdjointImage K F :=
  MulEquiv.ofBijective (e6PositiveFixedProjection K F)
    ⟨e6PositiveFixedProjection_injective K F, e6PositiveFixedProjection_surjective K F⟩

@[simp] theorem e6PositiveFixedProjectionEquiv_val (g : companionPositiveFixedSubgroup F K) :
    (e6PositiveFixedProjectionEquiv K F g).val =
      selectedWeightCompanionRho .E6 K g.val := rfl

/-- Fixed points commute with taking this image because rho is injective on U. -/
theorem e6PositiveFixedProjection_image :
    (companionPositiveFixedSubgroup F K).map (selectedWeightCompanionRho .E6 K) =
      e6PositiveFixedAdjointImage K F := by
  ext a
  constructor
  · intro ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    exact (e6PositiveFixedProjection K F ⟨g, hg⟩).property
  · intro ha
    obtain ⟨g, hg⟩ := e6PositiveFixedProjection_surjective K F ⟨a, ha⟩
    exact Subgroup.mem_map.mpr ⟨g.val, g.property, congrArg Subtype.val hg⟩

/-- The same positive count in the literal adjoint image, including q=2. -/
theorem e6PositiveFixedAdjointImage_card (hdeg : Module.finrank F K = 2) :
    Nat.card (e6PositiveFixedAdjointImage K F) = Nat.card F ^ 36 := by
  calc
    _ = Nat.card (companionPositiveFixedSubgroup F K) :=
      (Nat.card_congr (e6PositiveFixedProjectionEquiv K F).toEquiv).symm
    _ = Nat.card F ^ 36 := companionPositiveFixedSubgroup_card K F hdeg

end Atlas.Chevalley.TwistedE6
