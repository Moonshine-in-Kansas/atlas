import Atlas.LinearGroups.Chevalley.TwistedE6.PairParametersGeneric
import Atlas.LinearGroups.Chevalley.TwistedE6.FixedSimpleRoots

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
namespace TwistedE6
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

omit [Finite K] in
theorem simpleX_pair_parameters_injective (i : Fin 6) (hi : simpleNode i ≠ i) :
    Function.Injective (fun p : K × K =>
      selectedWeightCompanionX .E6 K i p.1 *
      selectedWeightCompanionX .E6 K (simpleNode i) p.2) := by
  intro s t h
  apply adjointX_simple_pair_injective
    (rootDatum .E6).pairing (rootDatum .E6).base K
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6)
    ((rootDatum .E6).indexEquiv i) ((rootDatum .E6).indexEquiv (simpleNode i))
    (fun he => hi ((rootDatum .E6).indexEquiv.injective he).symm)
  simpa only [map_mul, selectedWeightCompanionRho_X, modelX] using
    congrArg (selectedWeightCompanionRho .E6 K) h

omit [Finite K] in
theorem simpleY_pair_parameters_injective (i : Fin 6) (hi : simpleNode i ≠ i) :
    Function.Injective (fun p : K × K =>
      selectedWeightCompanionY .E6 K i p.1 *
      selectedWeightCompanionY .E6 K (simpleNode i) p.2) := by
  intro s t h
  apply adjointY_simple_pair_injective
    (rootDatum .E6).pairing (rootDatum .E6).base K
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6)
    ((rootDatum .E6).indexEquiv i) ((rootDatum .E6).indexEquiv (simpleNode i))
    (fun he => hi ((rootDatum .E6).indexEquiv.injective he).symm)
  simpa only [map_mul, selectedWeightCompanionRho_Y, modelY] using
    congrArg (selectedWeightCompanionRho .E6 K) h

theorem fixedPairXHom_injective (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) :
    Function.Injective (fixedPairXHom F K hdeg i hi) := by
  intro s t h
  have hp : (s.toAdd, Atlas.FiniteQuadratic.conjugation F K s.toAdd) =
      (t.toAdd, Atlas.FiniteQuadratic.conjugation F K t.toAdd) := by
    apply simpleX_pair_parameters_injective K i hi
    exact congrArg (fun g : companionFixedSubgroup F K => g.val) h
  exact Multiplicative.toAdd.injective (congrArg Prod.fst hp)

theorem fixedPairYHom_injective (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) :
    Function.Injective (fixedPairYHom F K hdeg i hi) := by
  intro s t h
  have hp : (s.toAdd, Atlas.FiniteQuadratic.conjugation F K s.toAdd) =
      (t.toAdd, Atlas.FiniteQuadratic.conjugation F K t.toAdd) := by
    apply simpleY_pair_parameters_injective K i hi
    exact congrArg (fun g : companionFixedSubgroup F K => g.val) h
  exact Multiplicative.toAdd.injective (congrArg Prod.fst hp)

theorem simpleX_pair_fixed_iff (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) (s t : K) :
    selectedWeightCompanionX .E6 K i s *
      selectedWeightCompanionX .E6 K (simpleNode i) t ∈ companionFixedSubgroup F K ↔
      t = Atlas.FiniteQuadratic.conjugation F K s := by
  constructor
  · intro h
    change companionTwist F K (_ * _) = _ at h
    rw [map_mul, companionTwist_X_conjugation, companionTwist_X_conjugation,
      simpleNode_involutive] at h
    have hcomm := (simpleX_diagram_commute K i hi
      (Atlas.FiniteQuadratic.conjugation F K t)
      (Atlas.FiniteQuadratic.conjugation F K s)).eq
    have hp : (Atlas.FiniteQuadratic.conjugation F K t,
        Atlas.FiniteQuadratic.conjugation F K s) = (s, t) :=
      simpleX_pair_parameters_injective K i hi (hcomm.trans h)
    exact (congrArg Prod.snd hp).symm
  · rintro rfl
    exact simpleX_pair_fixed F K hdeg i hi s

theorem simpleY_pair_fixed_iff (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) (s t : K) :
    selectedWeightCompanionY .E6 K i s *
      selectedWeightCompanionY .E6 K (simpleNode i) t ∈ companionFixedSubgroup F K ↔
      t = Atlas.FiniteQuadratic.conjugation F K s := by
  constructor
  · intro h
    change companionTwist F K (_ * _) = _ at h
    rw [map_mul, companionTwist_Y_conjugation, companionTwist_Y_conjugation,
      simpleNode_involutive] at h
    have hcomm := (simpleY_diagram_commute K i hi
      (Atlas.FiniteQuadratic.conjugation F K t)
      (Atlas.FiniteQuadratic.conjugation F K s)).eq
    have hp : (Atlas.FiniteQuadratic.conjugation F K t,
        Atlas.FiniteQuadratic.conjugation F K s) = (s, t) :=
      simpleY_pair_parameters_injective K i hi (hcomm.trans h)
    exact (congrArg Prod.snd hp).symm
  · rintro rfl
    exact simpleY_pair_fixed F K hdeg i hi s

/-- The entire fixed part of the two-root product is parametrized by K. -/
theorem mem_fixedPairXHom_range_iff (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) (g : companionFixedSubgroup F K) :
    g ∈ (fixedPairXHom F K hdeg i hi).range ↔
      ∃ s t : K, selectedWeightCompanionX .E6 K i s *
        selectedWeightCompanionX .E6 K (simpleNode i) t = g.val := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, Atlas.FiniteQuadratic.conjugation F K t.toAdd, rfl⟩
  · rintro ⟨s, t, h⟩
    have ht := (simpleX_pair_fixed_iff F K hdeg i hi s t).mp
      (h.symm ▸ g.property)
    refine ⟨Multiplicative.ofAdd s, Subtype.ext ?_⟩
    simpa only [fixedPairXHom_val, toAdd_ofAdd, ht] using h

theorem mem_fixedPairYHom_range_iff (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) (g : companionFixedSubgroup F K) :
    g ∈ (fixedPairYHom F K hdeg i hi).range ↔
      ∃ s t : K, selectedWeightCompanionY .E6 K i s *
        selectedWeightCompanionY .E6 K (simpleNode i) t = g.val := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, Atlas.FiniteQuadratic.conjugation F K t.toAdd, rfl⟩
  · rintro ⟨s, t, h⟩
    have ht := (simpleY_pair_fixed_iff F K hdeg i hi s t).mp
      (h.symm ▸ g.property)
    refine ⟨Multiplicative.ofAdd s, Subtype.ext ?_⟩
    simpa only [fixedPairYHom_val, toAdd_ofAdd, ht] using h

def fixedPairXEquiv (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) :
    Multiplicative K ≃* (fixedPairXHom F K hdeg i hi).range :=
  MonoidHom.ofInjective (fixedPairXHom_injective F K hdeg i hi)

def fixedPairYEquiv (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) :
    Multiplicative K ≃* (fixedPairYHom F K hdeg i hi).range :=
  MonoidHom.ofInjective (fixedPairYHom_injective F K hdeg i hi)

theorem fixedPairX_card (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) :
    Nat.card (fixedPairXHom F K hdeg i hi).range = Nat.card K :=
  (Nat.card_congr (fixedPairXEquiv F K hdeg i hi).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem fixedPairY_card (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) :
    Nat.card (fixedPairYHom F K hdeg i hi).range = Nat.card K :=
  (Nat.card_congr (fixedPairYEquiv F K hdeg i hi).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem fixedPairX_card_base (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) :
    Nat.card (fixedPairXHom F K hdeg i hi).range = Nat.card F ^ 2 := by
  rw [fixedPairX_card, Atlas.FiniteQuadratic.card_extension hdeg]

theorem fixedPairY_card_base (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) :
    Nat.card (fixedPairYHom F K hdeg i hi).range = Nat.card F ^ 2 := by
  rw [fixedPairY_card, Atlas.FiniteQuadratic.card_extension hdeg]

end TwistedE6
end Atlas.Chevalley
