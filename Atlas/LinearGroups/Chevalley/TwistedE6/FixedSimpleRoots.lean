import Atlas.LinearGroups.Chevalley.TwistedE6.CompanionTwist
import Atlas.LinearGroups.Chevalley.WeightCompanionNonAdjacentWeyl
import Atlas.GroupTheory.GraphFieldRootPairs

/-! Actual fixed simple root groups. This pending continuation is not part of
the sealed graph-lift checkpoint. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6
open Classical Atlas.GroupTheory
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem simpleNode_moved_cartan (i : Fin 6) (hi : simpleNode i ≠ i) :
    (rootDatum .E6).base.cartanMatrix ((rootDatum .E6).indexEquiv (simpleNode i))
      ((rootDatum .E6).indexEquiv i) = 0 := by
  change E6Data.base.cartanMatrix (E6Data.baseIndexEquiv (simpleNode i))
    (E6Data.baseIndexEquiv i) = 0
  rw [E6Data.base_cartan]
  fin_cases i <;> first | rfl | exact False.elim (hi rfl)

omit [Finite K] in
theorem simpleX_diagram_commute (i : Fin 6) (hi : simpleNode i ≠ i) (s t : K) :
    Commute (selectedWeightCompanionX .E6 K i s)
      (selectedWeightCompanionX .E6 K (simpleNode i) t) :=
  weightCompanionX_commute_of_zero_cartan
    (rootDatum .E6).pairing (rootDatum .E6).base (rootDatum_simpleDiamondProducts .E6)
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K _ _
    (fun h => hi ((rootDatum .E6).indexEquiv.injective h).symm)
    (simpleNode_moved_cartan i hi) s t

omit [Finite K] in
theorem simpleY_diagram_commute (i : Fin 6) (hi : simpleNode i ≠ i) (s t : K) :
    Commute (selectedWeightCompanionY .E6 K i s)
      (selectedWeightCompanionY .E6 K (simpleNode i) t) :=
  weightCompanionY_commute_of_zero_cartan
    (rootDatum .E6).pairing (rootDatum .E6).base (rootDatum_simpleDiamondProducts .E6)
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K _ _
    (fun h => hi ((rootDatum .E6).indexEquiv.injective h).symm)
    (simpleNode_moved_cartan i hi) s t

theorem companionTwist_X_conjugation (i : Fin 6) (t : K) :
    companionTwist F K (selectedWeightCompanionX .E6 K i t) =
      selectedWeightCompanionX .E6 K (simpleNode i) (Atlas.FiniteQuadratic.conjugation F K t) := by
  rw [companionTwist_X, Atlas.FiniteQuadratic.conjugation_apply]

theorem companionTwist_Y_conjugation (i : Fin 6) (t : K) :
    companionTwist F K (selectedWeightCompanionY .E6 K i t) =
      selectedWeightCompanionY .E6 K (simpleNode i) (Atlas.FiniteQuadratic.conjugation F K t) := by
  rw [companionTwist_Y, Atlas.FiniteQuadratic.conjugation_apply]

theorem simpleX_base_fixed (i : Fin 6) (hi : simpleNode i = i) (t : F) :
    selectedWeightCompanionX .E6 K i (algebraMap F K t) ∈ companionFixedSubgroup F K := by
  change companionTwist F K _ = _
  rw [companionTwist_X_conjugation, hi, Atlas.FiniteQuadratic.conjugation_base, MonoidHom.id_apply]

theorem simpleY_base_fixed (i : Fin 6) (hi : simpleNode i = i) (t : F) :
    selectedWeightCompanionY .E6 K i (algebraMap F K t) ∈ companionFixedSubgroup F K := by
  change companionTwist F K _ = _
  rw [companionTwist_Y_conjugation, hi, Atlas.FiniteQuadratic.conjugation_base, MonoidHom.id_apply]

omit [Finite K] in
theorem simpleX_parameter_injective (i : Fin 6) :
    Function.Injective (selectedWeightCompanionX .E6 K i) := by
  intro s t h
  apply modelX_injective .E6 K i
  exact congrArg (selectedWeightCompanionRho .E6 K) h

omit [Finite K] in
theorem simpleY_parameter_injective (i : Fin 6) :
    Function.Injective (selectedWeightCompanionY .E6 K i) := by
  intro s t h
  apply modelY_injective .E6 K i
  exact congrArg (selectedWeightCompanionRho .E6 K) h

theorem simpleX_fixed_iff (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i = i) (t : K) :
    selectedWeightCompanionX .E6 K i t ∈ companionFixedSubgroup F K ↔
      ∃ a : F, algebraMap F K a = t := by
  change companionTwist F K _ = _ ↔ _
  rw [companionTwist_X_conjugation, hi, MonoidHom.id_apply,
    (simpleX_parameter_injective K i).eq_iff]
  exact Atlas.FiniteQuadratic.conjugation_fixed_iff hdeg t

theorem simpleY_fixed_iff (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i = i) (t : K) :
    selectedWeightCompanionY .E6 K i t ∈ companionFixedSubgroup F K ↔
      ∃ a : F, algebraMap F K a = t := by
  change companionTwist F K _ = _ ↔ _
  rw [companionTwist_Y_conjugation, hi, MonoidHom.id_apply,
    (simpleY_parameter_injective K i).eq_iff]
  exact Atlas.FiniteQuadratic.conjugation_fixed_iff hdeg t

theorem simpleX_pair_fixed (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) (t : K) :
    selectedWeightCompanionX .E6 K i t *
      selectedWeightCompanionX .E6 K (simpleNode i) (Atlas.FiniteQuadratic.conjugation F K t) ∈
      companionFixedSubgroup F K := by
  change companionTwist F K (_ * _) = _
  rw [map_mul, companionTwist_X_conjugation, companionTwist_X_conjugation,
    simpleNode_involutive, Atlas.FiniteQuadratic.conjugation_conjugation hdeg]
  exact (simpleX_diagram_commute K i hi t _).eq.symm

theorem simpleY_pair_fixed (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) (t : K) :
    selectedWeightCompanionY .E6 K i t *
      selectedWeightCompanionY .E6 K (simpleNode i) (Atlas.FiniteQuadratic.conjugation F K t) ∈
      companionFixedSubgroup F K := by
  change companionTwist F K (_ * _) = _
  rw [map_mul, companionTwist_Y_conjugation, companionTwist_Y_conjugation,
    simpleNode_involutive, Atlas.FiniteQuadratic.conjugation_conjugation hdeg]
  exact (simpleY_diagram_commute K i hi t _).eq.symm

def fixedPairXHom (hdeg : Module.finrank F K = 2) (i : Fin 6) (hi : simpleNode i ≠ i) :
    Multiplicative K →* companionFixedSubgroup F K :=
  exchangedRootPairHom (companionTwist F K)
    (Atlas.FiniteQuadratic.conjugation F K).toAddEquiv.toMultiplicative
    (fun t => Atlas.FiniteQuadratic.conjugation_involutive hdeg t)
    (weightCompanionXHom (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K ((rootDatum .E6).indexEquiv i))
    (weightCompanionXHom (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K ((rootDatum .E6).indexEquiv (simpleNode i)))
    (fun t => companionTwist_X_conjugation F K i t.toAdd)
    (fun t => by
      change companionTwist F K (selectedWeightCompanionX .E6 K (simpleNode i) t.toAdd) = _
      rw [companionTwist_X_conjugation, simpleNode_involutive]
      rfl)
    (fun s t => simpleX_diagram_commute K i hi s.toAdd t.toAdd)

def fixedPairYHom (hdeg : Module.finrank F K = 2) (i : Fin 6) (hi : simpleNode i ≠ i) :
    Multiplicative K →* companionFixedSubgroup F K :=
  exchangedRootPairHom (companionTwist F K)
    (Atlas.FiniteQuadratic.conjugation F K).toAddEquiv.toMultiplicative
    (fun t => Atlas.FiniteQuadratic.conjugation_involutive hdeg t)
    (weightCompanionYHom (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K ((rootDatum .E6).indexEquiv i))
    (weightCompanionYHom (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K ((rootDatum .E6).indexEquiv (simpleNode i)))
    (fun t => companionTwist_Y_conjugation F K i t.toAdd)
    (fun t => by
      change companionTwist F K (selectedWeightCompanionY .E6 K (simpleNode i) t.toAdd) = _
      rw [companionTwist_Y_conjugation, simpleNode_involutive]
      rfl)
    (fun s t => simpleY_diagram_commute K i hi s.toAdd t.toAdd)

@[simp] theorem fixedPairXHom_val (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) (t : Multiplicative K) :
    (fixedPairXHom F K hdeg i hi t).val = selectedWeightCompanionX .E6 K i t.toAdd *
      selectedWeightCompanionX .E6 K (simpleNode i) (Atlas.FiniteQuadratic.conjugation F K t.toAdd) := rfl

@[simp] theorem fixedPairYHom_val (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i ≠ i) (t : Multiplicative K) :
    (fixedPairYHom F K hdeg i hi t).val = selectedWeightCompanionY .E6 K i t.toAdd *
      selectedWeightCompanionY .E6 K (simpleNode i) (Atlas.FiniteQuadratic.conjugation F K t.toAdd) := rfl

/-- The literal inherited three-factor Weyl word, with parameter one. -/
def simpleWeyl (i : Fin 6) : SelectedWeightCompanion .E6 K :=
  selectedWeightCompanionX .E6 K i 1 * selectedWeightCompanionY .E6 K i (-1) *
    selectedWeightCompanionX .E6 K i 1

theorem companionTwist_simpleWeyl (i : Fin 6) :
    companionTwist F K (simpleWeyl K i) = simpleWeyl K (simpleNode i) := by
  simp only [simpleWeyl, map_mul, companionTwist_X_conjugation,
    companionTwist_Y_conjugation, map_neg, map_one]

omit [Finite K] in
theorem simpleWeyl_diagram_commute (i : Fin 6) (hi : simpleNode i ≠ i) :
    Commute (simpleWeyl K i) (simpleWeyl K (simpleNode i)) := by
  exact weightCompanionWeyl_commute_of_zero_cartan
    (rootDatum .E6).pairing (rootDatum .E6).base (rootDatum_simpleDiamondProducts .E6)
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K _ _
    (fun h => hi ((rootDatum .E6).indexEquiv.injective h).symm)
    (simpleNode_moved_cartan i hi) 1 1

theorem simpleWeyl_fixed (i : Fin 6) (hi : simpleNode i = i) :
    simpleWeyl K i ∈ companionFixedSubgroup F K := by
  change companionTwist F K _ = _
  rw [companionTwist_simpleWeyl, hi, MonoidHom.id_apply]

theorem simpleWeyl_pair_fixed (i : Fin 6) (hi : simpleNode i ≠ i) :
    simpleWeyl K i * simpleWeyl K (simpleNode i) ∈ companionFixedSubgroup F K := by
  change companionTwist F K (_ * _) = _
  rw [map_mul, companionTwist_simpleWeyl, companionTwist_simpleWeyl, simpleNode_involutive]
  exact (simpleWeyl_diagram_commute K i hi).eq.symm

end Atlas.Chevalley.TwistedE6
