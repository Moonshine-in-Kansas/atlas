import Atlas.LinearGroups.Chevalley.TwistedE6.FoldedWeylRepresentatives
import Atlas.LinearGroups.Chevalley.TwistedE6.SingletonParameters
import Atlas.LinearGroups.Chevalley.TwistedE6.PairParametersTwisted

/-! Explicit positive-root witnesses and their fixed parameter groups. The
transporters are actual fixed normalizer elements. This does not assert that
the product of these groups is a subgroup or a full positive normal form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice

abbrev FixedPositiveLabel := {i : Fin 36 // positiveDiagram i = i}
abbrev PairedPositiveLabel := {i : Fin 36 // i < positiveDiagram i}

theorem card_fixedPositiveLabel : Fintype.card FixedPositiveLabel = 12 :=
  positiveDiagram_fixed_count

theorem card_pairedPositiveLabel : Fintype.card PairedPositiveLabel = 12 :=
  positiveDiagram_pair_count

def foldedPositiveLabel (i : Fin 36) : E6Data.Root :=
  ⟨rootRepresentative i, rootRepresentative_norm i⟩

variable (K : Type*) [Field K]

def foldedRootLift (i : Fin 36) :
    WeightCompanionRootLift (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K (foldedPositiveLabel i) where
  simple := (rootDatum .E6).indexEquiv (E6Data.nodeEquiv (foldedRootSeed i))
  lift := foldedWeylWordInN K (foldedRootWord i)
  root_eq := by
    have hs : ((rootDatum .E6).indexEquiv (E6Data.nodeEquiv (foldedRootSeed i))).val =
        E6Data.simpleRoot (foldedRootSeed i) := by
      change (E6Data.baseIndexEquiv (E6Data.nodeEquiv (foldedRootSeed i))).val = _
      rw [E6Data.baseIndexEquiv_apply, Equiv.symm_apply_apply]
    change companionNormalizerRootAction K (foldedWeylWordInN K (foldedRootWord i))
      ((rootDatum .E6).indexEquiv (E6Data.nodeEquiv (foldedRootSeed i))).val = _
    rw [hs]
    exact Subtype.ext (foldedWeylWordInN_representative K i)

/-- Use the same transporter for the diagram partner, so no unproved
independence from the choice of a root lift is needed. -/
def foldedPartnerRootLift (i : Fin 36) :
    WeightCompanionRootLift (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K (foldedPositiveLabel (positiveDiagram i)) where
  simple := (rootDatum .E6).indexEquiv (E6Data.nodeEquiv (latticeNode (foldedRootSeed i)))
  lift := foldedWeylWordInN K (foldedRootWord i)
  root_eq := by
    have hs : ((rootDatum .E6).indexEquiv
        (E6Data.nodeEquiv (latticeNode (foldedRootSeed i)))).val =
        E6Data.simpleRoot (latticeNode (foldedRootSeed i)) := by
      change (E6Data.baseIndexEquiv
        (E6Data.nodeEquiv (latticeNode (foldedRootSeed i)))).val = _
      rw [E6Data.baseIndexEquiv_apply, Equiv.symm_apply_apply]
    change companionNormalizerRootAction K (foldedWeylWordInN K (foldedRootWord i))
      ((rootDatum .E6).indexEquiv
        (E6Data.nodeEquiv (latticeNode (foldedRootSeed i)))).val = _
    rw [hs]
    apply Subtype.ext
    rw [foldedWeylWordInN_rootAction]
    exact foldedRootWord_partner i

def foldedRootHom (i : Fin 36) : Multiplicative K →* SelectedWeightCompanion .E6 K :=
  weightCompanionRootLiftHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K (foldedRootLift K i)

def foldedPartnerRootHom (i : Fin 36) : Multiplicative K →* SelectedWeightCompanion .E6 K :=
  weightCompanionRootLiftHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K (foldedPartnerRootLift K i)

theorem foldedRootHom_apply (i : Fin 36) (t : Multiplicative K) :
    foldedRootHom K i t =
      (foldedWeylWordInN K (foldedRootWord i)).val *
        selectedWeightCompanionX .E6 K (E6Data.nodeEquiv (foldedRootSeed i)) t.toAdd *
        (foldedWeylWordInN K (foldedRootWord i)).val⁻¹ := rfl

theorem foldedPartnerRootHom_apply (i : Fin 36) (t : Multiplicative K) :
    foldedPartnerRootHom K i t =
      (foldedWeylWordInN K (foldedRootWord i)).val *
        selectedWeightCompanionX .E6 K
          (E6Data.nodeEquiv (latticeNode (foldedRootSeed i))) t.toAdd *
        (foldedWeylWordInN K (foldedRootWord i)).val⁻¹ := rfl

variable (F : Type*) [Field F] [Finite F] [Finite K] [Algebra F K]

def positiveRootWordFixed (i : Fin 36) : companionFixedSubgroup F K :=
  ⟨(foldedWeylWordInN K (foldedRootWord i)).val,
    foldedWeylWordInN_fixed K F (foldedRootWord i)⟩

def positiveSingletonXHom (i : FixedPositiveLabel) :
    Multiplicative F →* companionFixedSubgroup F K :=
  (MulAut.conj (positiveRootWordFixed K F i.val)).toMonoidHom.comp
    (fixedSingletonXHom F K 3 rfl)

def positivePairXHom (hdeg : Module.finrank F K = 2) (i : PairedPositiveLabel) :
    Multiplicative K →* companionFixedSubgroup F K :=
  (MulAut.conj (positiveRootWordFixed K F i.val)).toMonoidHom.comp
    (fixedPairXHom F K hdeg 0 (by decide))

theorem positiveSingletonXHom_injective (i : FixedPositiveLabel) :
    Function.Injective (positiveSingletonXHom K F i) :=
  (MulAut.conj (positiveRootWordFixed K F i.val)).injective.comp
    (fixedSingletonXHom_injective F K 3 rfl)

theorem positivePairXHom_injective (hdeg : Module.finrank F K = 2)
    (i : PairedPositiveLabel) : Function.Injective (positivePairXHom K F hdeg i) :=
  (MulAut.conj (positiveRootWordFixed K F i.val)).injective.comp
    (fixedPairXHom_injective F K hdeg 0 (by decide))

def positiveSingletonXEquiv (i : FixedPositiveLabel) :
    Multiplicative F ≃* (positiveSingletonXHom K F i).range :=
  MonoidHom.ofInjective (positiveSingletonXHom_injective K F i)

def positivePairXEquiv (hdeg : Module.finrank F K = 2) (i : PairedPositiveLabel) :
    Multiplicative K ≃* (positivePairXHom K F hdeg i).range :=
  MonoidHom.ofInjective (positivePairXHom_injective K F hdeg i)

theorem positiveSingletonX_card (i : FixedPositiveLabel) :
    Nat.card (positiveSingletonXHom K F i).range = Nat.card F :=
  (Nat.card_congr (positiveSingletonXEquiv K F i).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem positivePairX_card (hdeg : Module.finrank F K = 2) (i : PairedPositiveLabel) :
    Nat.card (positivePairXHom K F hdeg i).range = Nat.card F ^ 2 := by
  calc
    _ = Nat.card K :=
      (Nat.card_congr (positivePairXEquiv K F hdeg i).toEquiv).symm.trans
        (Nat.card_congr Multiplicative.toAdd)
    _ = Nat.card F ^ 2 := Atlas.FiniteQuadratic.card_extension hdeg

theorem positiveSingletonXHom_eq_rootHom (i : FixedPositiveLabel) (t : Multiplicative F) :
    (positiveSingletonXHom K F i t).val =
      foldedRootHom K i.val (Multiplicative.ofAdd (algebraMap F K t.toAdd)) := by
  rw [foldedRootHom_apply]
  simp only [foldedRootSeed, i.property, ite_true]
  rfl

theorem positivePairXHom_eq_rootHom (hdeg : Module.finrank F K = 2)
    (i : PairedPositiveLabel) (t : Multiplicative K) :
    (positivePairXHom K F hdeg i t).val =
      foldedRootHom K i.val t * foldedPartnerRootHom K i.val
        (Multiplicative.ofAdd (Atlas.FiniteQuadratic.conjugation F K t.toAdd)) := by
  have hi : positiveDiagram i.val ≠ i.val := ne_of_gt i.property
  rw [foldedRootHom_apply, foldedPartnerRootHom_apply]
  simp only [foldedRootSeed, hi, ite_false, toAdd_ofAdd]
  change _ * (_ * _) * _⁻¹ = (_ * _ * _⁻¹) * (_ * _ * _⁻¹)
  group
  rfl

theorem foldedRootHom_fixed_iff (hdeg : Module.finrank F K = 2)
    (i : FixedPositiveLabel) (t : K) :
    foldedRootHom K i.val (Multiplicative.ofAdd t) ∈ companionFixedSubgroup F K ↔
      ∃ a : F, algebraMap F K a = t := by
  rw [foldedRootHom_apply]
  simp only [foldedRootSeed, i.property, ite_true, toAdd_ofAdd]
  rw [(companionFixedSubgroup F K).mul_mem_cancel_right
      ((companionFixedSubgroup F K).inv_mem
        (foldedWeylWordInN_fixed K F (foldedRootWord i.val))),
    (companionFixedSubgroup F K).mul_mem_cancel_left
      (foldedWeylWordInN_fixed K F (foldedRootWord i.val))]
  exact simpleX_fixed_iff F K hdeg 3 rfl t

theorem foldedRootPair_fixed_iff (hdeg : Module.finrank F K = 2)
    (i : PairedPositiveLabel) (s t : K) :
    foldedRootHom K i.val (Multiplicative.ofAdd s) *
        foldedPartnerRootHom K i.val (Multiplicative.ofAdd t) ∈
      companionFixedSubgroup F K ↔ t = Atlas.FiniteQuadratic.conjugation F K s := by
  have hi : positiveDiagram i.val ≠ i.val := ne_of_gt i.property
  rw [foldedRootHom_apply, foldedPartnerRootHom_apply]
  simp only [foldedRootSeed, hi, ite_false, toAdd_ofAdd]
  have he (n a b : SelectedWeightCompanion .E6 K) :
      (n * a * n⁻¹) * (n * b * n⁻¹) = n * (a * b) * n⁻¹ := by group
  rw [he, (companionFixedSubgroup F K).mul_mem_cancel_right
      ((companionFixedSubgroup F K).inv_mem
        (foldedWeylWordInN_fixed K F (foldedRootWord i.val))),
    (companionFixedSubgroup F K).mul_mem_cancel_left
      (foldedWeylWordInN_fixed K F (foldedRootWord i.val))]
  exact simpleX_pair_fixed_iff F K hdeg 0 (by decide) s t

end Atlas.Chevalley.TwistedE6
