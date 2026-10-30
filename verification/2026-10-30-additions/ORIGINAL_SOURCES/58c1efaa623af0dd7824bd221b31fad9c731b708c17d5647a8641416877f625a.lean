import FamilyWork.FixedSimpleRoots

/-! The full fixed simple-root subgroups at diagram-fixed nodes are copies of
the additive base field. The opposite root groups are treated separately. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def fixedSingletonXHom (i : Fin 6) (hi : simpleNode i = i) :
    Multiplicative F →* companionFixedSubgroup F K :=
  ((weightCompanionXHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K ((rootDatum .E6).indexEquiv i)).comp
      (algebraMap F K).toAddMonoidHom.toMultiplicative).codRestrict
    (companionFixedSubgroup F K) (fun t => simpleX_base_fixed F K i hi t.toAdd)

def fixedSingletonYHom (i : Fin 6) (hi : simpleNode i = i) :
    Multiplicative F →* companionFixedSubgroup F K :=
  ((weightCompanionYHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K ((rootDatum .E6).indexEquiv i)).comp
      (algebraMap F K).toAddMonoidHom.toMultiplicative).codRestrict
    (companionFixedSubgroup F K) (fun t => simpleY_base_fixed F K i hi t.toAdd)

@[simp] theorem fixedSingletonXHom_val (i : Fin 6) (hi : simpleNode i = i)
    (t : Multiplicative F) :
    (fixedSingletonXHom F K i hi t).val =
      selectedWeightCompanionX .E6 K i (algebraMap F K t.toAdd) := rfl

@[simp] theorem fixedSingletonYHom_val (i : Fin 6) (hi : simpleNode i = i)
    (t : Multiplicative F) :
    (fixedSingletonYHom F K i hi t).val =
      selectedWeightCompanionY .E6 K i (algebraMap F K t.toAdd) := rfl

theorem fixedSingletonXHom_injective (i : Fin 6) (hi : simpleNode i = i) :
    Function.Injective (fixedSingletonXHom F K i hi) := by
  intro s t h
  have hp : algebraMap F K s.toAdd = algebraMap F K t.toAdd := by
    apply simpleX_parameter_injective K i
    exact congrArg (fun g : companionFixedSubgroup F K => g.val) h
  exact Multiplicative.toAdd.injective ((algebraMap F K).injective hp)

theorem fixedSingletonYHom_injective (i : Fin 6) (hi : simpleNode i = i) :
    Function.Injective (fixedSingletonYHom F K i hi) := by
  intro s t h
  have hp : algebraMap F K s.toAdd = algebraMap F K t.toAdd := by
    apply simpleY_parameter_injective K i
    exact congrArg (fun g : companionFixedSubgroup F K => g.val) h
  exact Multiplicative.toAdd.injective ((algebraMap F K).injective hp)

theorem mem_fixedSingletonXHom_range_iff (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i = i) (g : companionFixedSubgroup F K) :
    g ∈ (fixedSingletonXHom F K i hi).range ↔
      ∃ t : K, selectedWeightCompanionX .E6 K i t = g.val := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨algebraMap F K t.toAdd, rfl⟩
  · rintro ⟨t, ht⟩
    obtain ⟨a, ha⟩ := (simpleX_fixed_iff F K hdeg i hi t).mp (ht.symm ▸ g.property)
    refine ⟨Multiplicative.ofAdd a, Subtype.ext ?_⟩
    simpa only [fixedSingletonXHom_val, toAdd_ofAdd, ha] using ht

theorem mem_fixedSingletonYHom_range_iff (hdeg : Module.finrank F K = 2)
    (i : Fin 6) (hi : simpleNode i = i) (g : companionFixedSubgroup F K) :
    g ∈ (fixedSingletonYHom F K i hi).range ↔
      ∃ t : K, selectedWeightCompanionY .E6 K i t = g.val := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨algebraMap F K t.toAdd, rfl⟩
  · rintro ⟨t, ht⟩
    obtain ⟨a, ha⟩ := (simpleY_fixed_iff F K hdeg i hi t).mp (ht.symm ▸ g.property)
    refine ⟨Multiplicative.ofAdd a, Subtype.ext ?_⟩
    simpa only [fixedSingletonYHom_val, toAdd_ofAdd, ha] using ht

def fixedSingletonXEquiv (i : Fin 6) (hi : simpleNode i = i) :
    Multiplicative F ≃* (fixedSingletonXHom F K i hi).range :=
  MonoidHom.ofInjective (fixedSingletonXHom_injective F K i hi)

def fixedSingletonYEquiv (i : Fin 6) (hi : simpleNode i = i) :
    Multiplicative F ≃* (fixedSingletonYHom F K i hi).range :=
  MonoidHom.ofInjective (fixedSingletonYHom_injective F K i hi)

theorem fixedSingletonX_card (i : Fin 6) (hi : simpleNode i = i) :
    Nat.card (fixedSingletonXHom F K i hi).range = Nat.card F :=
  (Nat.card_congr (fixedSingletonXEquiv F K i hi).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem fixedSingletonY_card (i : Fin 6) (hi : simpleNode i = i) :
    Nat.card (fixedSingletonYHom F K i hi).range = Nat.card F :=
  (Nat.card_congr (fixedSingletonYEquiv F K i hi).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

end Atlas.Chevalley.TwistedE6
