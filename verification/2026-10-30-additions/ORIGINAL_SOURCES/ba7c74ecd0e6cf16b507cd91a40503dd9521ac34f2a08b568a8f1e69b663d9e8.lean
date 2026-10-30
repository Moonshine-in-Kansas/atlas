import FamilyWork.PositiveRootTransport
import FamilyWork.PositiveCoordinates
import Mathlib.Algebra.Group.Commute.Basic

/-! one diagram-compatible system of positive-root lifts and parameters.

For a fixed or smaller label use its existing folded lift. For a larger label
use the partner lift attached to the smaller label, retaining that exact word
and changing only the proof of its target label. Thus an exchanged pair uses
one common normalizer word. No equality between arbitrary root markings is used.

Verification receipts are recorded separately. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice

theorem e6_simpleNode_nodeEquiv (j : Fin 6) :
    simpleNode (E6Data.nodeEquiv j) = E6Data.nodeEquiv (latticeNode j) := by
  simp [simpleNode]

@[simp] theorem e6PositiveRootEquiv_root (i : Fin 36) :
    (e6PositiveRootEquiv i).val = foldedPositiveLabel i := rfl

theorem e6PositiveRootEquiv_symm_root
    (β : {β : E6Data.Root // E6Data.base.IsPos β}) :
    foldedPositiveLabel (e6PositiveRootEquiv.symm β) = β.val := by
  change (e6PositiveRootEquiv (e6PositiveRootEquiv.symm β)).val = β.val
  exact congrArg Subtype.val (e6PositiveRootEquiv.apply_symm_apply β)

theorem e6PositiveRootEquiv_symm_coordinates
    (β : {β : E6Data.Root // E6Data.base.IsPos β}) :
    rootRepresentative (e6PositiveRootEquiv.symm β) = β.val.val :=
  congrArg Subtype.val (e6PositiveRootEquiv_symm_root β)

/-- The existing diagram permutation transported to the actual positive-root subtype. -/
def e6PositiveRootDiagram : Equiv.Perm {β : E6Data.Root // E6Data.base.IsPos β} :=
  e6PositiveRootEquiv.symm.trans (positiveDiagram.trans e6PositiveRootEquiv)

@[simp] theorem e6PositiveRootDiagram_equiv (i : Fin 36) :
    e6PositiveRootDiagram (e6PositiveRootEquiv i) =
      e6PositiveRootEquiv (positiveDiagram i) := by
  simp [e6PositiveRootDiagram]

@[simp] theorem e6PositiveRootDiagram_index
    (β : {β : E6Data.Root // E6Data.base.IsPos β}) :
    e6PositiveRootEquiv.symm (e6PositiveRootDiagram β) =
      positiveDiagram (e6PositiveRootEquiv.symm β) := by
  simp [e6PositiveRootDiagram]

theorem e6PositiveRootDiagram_involutive : Function.Involutive e6PositiveRootDiagram := by
  intro β
  apply e6PositiveRootEquiv.symm.injective
  simp only [e6PositiveRootDiagram_index, positiveDiagram_involutive (e6PositiveRootEquiv.symm β)]

/-- The transported action is the actual integral-root diagram action. -/
theorem e6PositiveRootDiagram_root
    (β : {β : E6Data.Root // E6Data.base.IsPos β}) :
    (e6PositiveRootDiagram β).val = rootDiagram β.val := by
  obtain ⟨i, rfl⟩ := e6PositiveRootEquiv.surjective β
  rw [e6PositiveRootDiagram_equiv, e6PositiveRootEquiv_root, e6PositiveRootEquiv_root]
  apply Subtype.ext
  change rootRepresentative (positiveDiagram i) = latticeDiagram ℤ (rootRepresentative i)
  exact (latticeDiagram_rootRepresentative i).symm

theorem e6PositiveRootDiagram_coordinates
    (β : {β : E6Data.Root // E6Data.base.IsPos β}) (j : Fin 6) :
    (e6PositiveRootDiagram β).val.val j = β.val.val (latticeNode j) := by
  simp only [e6PositiveRootDiagram_root, rootDiagram_val, latticeDiagram_apply]

variable (K : Type*) [Field K]

/-- The larger label retains the partner's simple root and the smaller label's word;
only its target equality is transported by the diagram involution. -/
def e6CompatibleRootLift (i : Fin 36) :
    WeightCompanionRootLift (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K (foldedPositiveLabel i) :=
  if i ≤ positiveDiagram i then foldedRootLift K i else
    { simple := (foldedPartnerRootLift K (positiveDiagram i)).simple
      lift := (foldedPartnerRootLift K (positiveDiagram i)).lift
      root_eq := by
        simpa only [positiveDiagram_involutive i] using
          (foldedPartnerRootLift K (positiveDiagram i)).root_eq }

theorem e6CompatibleRootLift_of_le (i : Fin 36) (hi : i ≤ positiveDiagram i) :
    e6CompatibleRootLift K i = foldedRootLift K i := by
  simp only [e6CompatibleRootLift, if_pos hi]

/-- The actual additive root homomorphism attached to the compatible witness. -/
def e6CompatibleRootHom (i : Fin 36) :
    Multiplicative K →* SelectedWeightCompanion .E6 K :=
  weightCompanionRootLiftHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K (e6CompatibleRootLift K i)

theorem e6CompatibleRootHom_of_le (i : Fin 36) (hi : i ≤ positiveDiagram i) :
    e6CompatibleRootHom K i = foldedRootHom K i := by
  simp only [e6CompatibleRootHom, e6CompatibleRootLift_of_le K i hi, foldedRootHom]

theorem e6CompatibleRootHom_of_gt (i : Fin 36) (hi : positiveDiagram i < i) :
    e6CompatibleRootHom K i = foldedPartnerRootHom K (positiveDiagram i) := by
  simp only [e6CompatibleRootHom, e6CompatibleRootLift, if_neg (not_le.mpr hi),
    foldedPartnerRootHom, weightCompanionRootLiftHom]

theorem e6CompatibleRootHom_diagram_of_lt (i : Fin 36) (hi : i < positiveDiagram i) :
    e6CompatibleRootHom K (positiveDiagram i) = foldedPartnerRootHom K i := by
  have hd : positiveDiagram (positiveDiagram i) < positiveDiagram i := by
    simpa only [positiveDiagram_involutive i] using hi
  rw [e6CompatibleRootHom_of_gt K (positiveDiagram i) hd, positiveDiagram_involutive]

/-- At a fixed root the partner construction has exactly the same simple root and word. -/
theorem e6_foldedPartnerRootHom_eq_of_fixed (i : Fin 36) (hi : positiveDiagram i = i) :
    foldedPartnerRootHom K i = foldedRootHom K i := by
  apply MonoidHom.ext
  intro t
  rw [foldedPartnerRootHom_apply, foldedRootHom_apply,
    (foldedRootSeed_fixed_iff i).mpr hi]

/-- These two homomorphisms use the same word, so simple-pair commutation transports. -/
theorem e6_foldedRootHom_partner_commute (i : Fin 36) (hi : positiveDiagram i ≠ i)
    (s t : Multiplicative K) :
    Commute (foldedRootHom K i s) (foldedPartnerRootHom K i t) := by
  have hs : simpleNode (E6Data.nodeEquiv (foldedRootSeed i)) ≠
      E6Data.nodeEquiv (foldedRootSeed i) := by
    rw [e6_simpleNode_nodeEquiv]
    intro he
    exact hi ((foldedRootSeed_fixed_iff i).mp (E6Data.nodeEquiv.injective he))
  have hc := simpleX_diagram_commute K (E6Data.nodeEquiv (foldedRootSeed i))
    hs s.toAdd t.toAdd
  rw [e6_simpleNode_nodeEquiv] at hc
  rw [foldedRootHom_apply, foldedPartnerRootHom_apply]
  exact hc.conj _

theorem e6CompatibleRootHom_diagram_commute (i : Fin 36) (hi : positiveDiagram i ≠ i)
    (s t : Multiplicative K) :
    Commute (e6CompatibleRootHom K i s) (e6CompatibleRootHom K (positiveDiagram i) t) := by
  by_cases hle : i ≤ positiveDiagram i
  · have hlt : i < positiveDiagram i := lt_of_le_of_ne hle (Ne.symm hi)
    rw [e6CompatibleRootHom_of_le K i hle, e6CompatibleRootHom_diagram_of_lt K i hlt]
    exact e6_foldedRootHom_partner_commute K i hi s t
  · have hgt : positiveDiagram i < i := lt_of_not_ge hle
    have hd : positiveDiagram i < positiveDiagram (positiveDiagram i) := by
      simpa only [positiveDiagram_involutive i] using hgt
    rw [e6CompatibleRootHom_of_gt K i hgt,
      e6CompatibleRootHom_of_le K (positiveDiagram i) hd.le]
    exact (e6_foldedRootHom_partner_commute K (positiveDiagram i) (ne_of_gt hd) t s).symm

/-- The same compatible witness, reindexed by an actual positive root. -/
def e6CompatiblePositiveRootLift (β : {β : E6Data.Root // E6Data.base.IsPos β}) :
    WeightCompanionRootLift (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K β.val where
  simple := (e6CompatibleRootLift K (e6PositiveRootEquiv.symm β)).simple
  lift := (e6CompatibleRootLift K (e6PositiveRootEquiv.symm β)).lift
  root_eq := (e6CompatibleRootLift K (e6PositiveRootEquiv.symm β)).root_eq.trans
    (e6PositiveRootEquiv_symm_root β)

def e6CompatiblePositiveRootHom (β : {β : E6Data.Root // E6Data.base.IsPos β}) :
    Multiplicative K →* SelectedWeightCompanion .E6 K :=
  weightCompanionRootLiftHom (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K (e6CompatiblePositiveRootLift K β)

theorem e6CompatiblePositiveRootHom_eq
    (β : {β : E6Data.Root // E6Data.base.IsPos β}) :
    e6CompatiblePositiveRootHom K β =
      e6CompatibleRootHom K (e6PositiveRootEquiv.symm β) := rfl

@[simp] theorem e6CompatiblePositiveRootHom_equiv (i : Fin 36) :
    e6CompatiblePositiveRootHom K (e6PositiveRootEquiv i) = e6CompatibleRootHom K i := by
  rw [e6CompatiblePositiveRootHom_eq, Equiv.symm_apply_apply]

theorem e6CompatiblePositiveRootHom_diagram_commute
    (β : {β : E6Data.Root // E6Data.base.IsPos β}) (hβ : e6PositiveRootDiagram β ≠ β)
    (s t : Multiplicative K) :
    Commute (e6CompatiblePositiveRootHom K β s)
      (e6CompatiblePositiveRootHom K (e6PositiveRootDiagram β) t) := by
  have hi : positiveDiagram (e6PositiveRootEquiv.symm β) ≠ e6PositiveRootEquiv.symm β := by
    intro he
    apply hβ
    apply e6PositiveRootEquiv.symm.injective
    simpa only [e6PositiveRootDiagram_index] using he
  simpa only [e6CompatiblePositiveRootHom_eq, e6PositiveRootDiagram_index] using
    e6CompatibleRootHom_diagram_commute K (e6PositiveRootEquiv.symm β) hi s t

/-- Plain field-parameter notation for the compatible root homomorphism. -/
def e6CompatibleRootX (i : Fin 36) (t : K) : SelectedWeightCompanion .E6 K :=
  e6CompatibleRootHom K i (Multiplicative.ofAdd t)

variable (F : Type*) [Field F] [Finite F] [Finite K] [Algebra F K]

/-- Apply graph--Frobenius to the exact shared-word conjugation formula. -/
theorem e6_companionTwist_foldedRootHom (i : Fin 36) (t : Multiplicative K) :
    companionTwist F K (foldedRootHom K i t) =
      foldedPartnerRootHom K i
        (Multiplicative.ofAdd (Atlas.FiniteQuadratic.conjugation F K t.toAdd)) := by
  have hn := foldedWeylWordInN_fixed K F (foldedRootWord i)
  change companionTwist F K (foldedWeylWordInN K (foldedRootWord i)).val =
    (foldedWeylWordInN K (foldedRootWord i)).val at hn
  rw [foldedRootHom_apply, foldedPartnerRootHom_apply]
  simp only [map_mul, map_inv, hn, companionTwist_X_conjugation,
    e6_simpleNode_nodeEquiv, toAdd_ofAdd]

/-- The reverse exchange uses the same word and only the node involution. -/
theorem e6_companionTwist_foldedPartnerRootHom (i : Fin 36) (t : Multiplicative K) :
    companionTwist F K (foldedPartnerRootHom K i t) =
      foldedRootHom K i
        (Multiplicative.ofAdd (Atlas.FiniteQuadratic.conjugation F K t.toAdd)) := by
  have hn := foldedWeylWordInN_fixed K F (foldedRootWord i)
  change companionTwist F K (foldedWeylWordInN K (foldedRootWord i)).val =
    (foldedWeylWordInN K (foldedRootWord i)).val at hn
  rw [foldedPartnerRootHom_apply, foldedRootHom_apply]
  simp only [map_mul, map_inv, hn, companionTwist_X_conjugation,
    e6_simpleNode_nodeEquiv, latticeNode_involutive (foldedRootSeed i), toAdd_ofAdd]

/-- Graph--Frobenius covariance for all 36 labels, including the fixed labels. -/
theorem e6CompatibleRootHom_twist (i : Fin 36) (t : Multiplicative K) :
    companionTwist F K (e6CompatibleRootHom K i t) =
      e6CompatibleRootHom K (positiveDiagram i)
        (Multiplicative.ofAdd (Atlas.FiniteQuadratic.conjugation F K t.toAdd)) := by
  by_cases hle : i ≤ positiveDiagram i
  · rw [e6CompatibleRootHom_of_le K i hle, e6_companionTwist_foldedRootHom K F]
    by_cases hfix : positiveDiagram i = i
    · rw [hfix, e6CompatibleRootHom_of_le K i hle,
        e6_foldedPartnerRootHom_eq_of_fixed K i hfix]
    · have hlt : i < positiveDiagram i := lt_of_le_of_ne hle (Ne.symm hfix)
      rw [e6CompatibleRootHom_diagram_of_lt K i hlt]
  · have hgt : positiveDiagram i < i := lt_of_not_ge hle
    have hd : positiveDiagram i ≤ positiveDiagram (positiveDiagram i) := by
      simpa only [positiveDiagram_involutive i] using hgt.le
    rw [e6CompatibleRootHom_of_gt K i hgt,
      e6_companionTwist_foldedPartnerRootHom K F,
      e6CompatibleRootHom_of_le K (positiveDiagram i) hd]

theorem e6CompatibleRootX_twist (i : Fin 36) (t : K) :
    companionTwist F K (e6CompatibleRootX K i t) =
      e6CompatibleRootX K (positiveDiagram i) (Atlas.FiniteQuadratic.conjugation F K t) :=
  e6CompatibleRootHom_twist K F i (Multiplicative.ofAdd t)

theorem e6CompatibleRootX_twist_of_fixed (i : Fin 36) (hi : positiveDiagram i = i) (t : K) :
    companionTwist F K (e6CompatibleRootX K i t) =
      e6CompatibleRootX K i (Atlas.FiniteQuadratic.conjugation F K t) := by
  simpa only [hi] using e6CompatibleRootX_twist K F i t

theorem e6CompatiblePositiveRootHom_twist
    (β : {β : E6Data.Root // E6Data.base.IsPos β}) (t : Multiplicative K) :
    companionTwist F K (e6CompatiblePositiveRootHom K β t) =
      e6CompatiblePositiveRootHom K (e6PositiveRootDiagram β)
        (Multiplicative.ofAdd (Atlas.FiniteQuadratic.conjugation F K t.toAdd)) := by
  simpa only [e6CompatiblePositiveRootHom_eq, e6PositiveRootDiagram_index] using
    e6CompatibleRootHom_twist K F (e6PositiveRootEquiv.symm β) t

/-- Existing singleton parameters expressed in the compatible marking. -/
theorem positiveSingletonXHom_eq_e6Compatible (i : FixedPositiveLabel) (t : Multiplicative F) :
    (positiveSingletonXHom K F i t).val =
      e6CompatibleRootHom K i.val (Multiplicative.ofAdd (algebraMap F K t.toAdd)) := by
  have hi : i.val ≤ positiveDiagram i.val := by
    simpa only [i.property] using (le_refl i.val)
  rw [positiveSingletonXHom_eq_rootHom, e6CompatibleRootHom_of_le K i.val hi]

/-- Existing paired parameters use the smaller word on both coordinates.
The original quadratic-extension hypothesis of `positivePairXHom` is retained. -/
theorem positivePairXHom_eq_e6Compatible (hdeg : Module.finrank F K = 2)
    (i : PairedPositiveLabel) (t : Multiplicative K) :
    (positivePairXHom K F hdeg i t).val =
      e6CompatibleRootHom K i.val t * e6CompatibleRootHom K (positiveDiagram i.val)
        (Multiplicative.ofAdd (Atlas.FiniteQuadratic.conjugation F K t.toAdd)) := by
  rw [positivePairXHom_eq_rootHom, e6CompatibleRootHom_of_le K i.val i.property.le,
    e6CompatibleRootHom_diagram_of_lt K i.val i.property]

end Atlas.Chevalley.TwistedE6
