import FamilyWork.PositiveFixedOrder
import FamilyWork.PositiveProjection
import FamilyWork.TorusTupleAction
import FamilyWork.FixedTorusOrder
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusJoin

/-! The literal fixed Borel B ∩ H in the selected simply connected E6 model.

Here B is the inherited `selectedWeightCompanionPositiveTorusJoin .E6 K`,
and H is the graph--Frobenius fixed subgroup. The inherited unique U*T
factorization and stability of both factors force the factors of a fixed
element to be fixed individually. Only after that argument do we identify
B ∩ H with the join of U ∩ H and T ∩ H.

The count uses only the new fixed-positive and fixed-torus counts, through
the displayed product equivalence. No split positive, split Borel, or
whole-group order formula is used in the counting proof.

Verification receipts are recorded separately. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Atlas.Chevalley.TwistedE6

section SplitStructure

variable (K : Type*) [Field K]

/-- Specialize the inherited normalization theorem to the actual E6 factors. -/
theorem e6Torus_le_positiveNormalizer :
    selectedWeightCompanionTorusSubgroup .E6 K ≤
      Subgroup.normalizer (selectedWeightCompanionPositiveSubgroup .E6 K) :=
  weightCompanionTorus_le_positiveWitnessedNormalizer
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K

/-- The existing faithful companion representation separates U and T. -/
theorem e6Positive_disjoint_torus :
    Disjoint (selectedWeightCompanionPositiveSubgroup .E6 K)
      (selectedWeightCompanionTorusSubgroup .E6 K) :=
  disjoint_iff.mpr
    (positiveWitnessedWeightCompanion_inf_torus_eq_bot
      (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6) K E6Data.simpleDiamondProducts)

/-- Reuse the existing unique decomposition of every element of the actual B. -/
theorem e6PositiveTorusJoin_existsUnique
    (g : selectedWeightCompanionPositiveTorusJoin .E6 K) :
    ∃! p : selectedWeightCompanionPositiveSubgroup .E6 K ×
      selectedWeightCompanionTorusSubgroup .E6 K,
      p.1.val * p.2.val = g.val :=
  positiveWitnessedTorusJoin_existsUnique
    (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K E6Data.simpleDiamondProducts g

end SplitStructure

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Whole-tuple covariance and the actual torus parametrization imply stability. -/
theorem e6TorusSubgroup_twist_mem (g : SelectedWeightCompanion .E6 K)
    (hg : g ∈ selectedWeightCompanionTorusSubgroup .E6 K) :
    companionTwist F K g ∈ selectedWeightCompanionTorusSubgroup .E6 K := by
  obtain ⟨s, hs⟩ := (e6PublicTorusParametersEquiv K).surjective ⟨g, hg⟩
  have hval : e6PublicTorusParameters K s = g :=
    congrArg (fun t : selectedWeightCompanionTorusSubgroup .E6 K => t.val) hs
  rw [← hval, companionTwist_e6PublicTorusParameters]
  exact e6PublicTorusParameters_mem K _

/-- Stability of the two actual factors gives stability of their inherited join. -/
theorem e6PositiveTorusJoin_twist_mem (g : SelectedWeightCompanion .E6 K)
    (hg : g ∈ selectedWeightCompanionPositiveTorusJoin .E6 K) :
    companionTwist F K g ∈ selectedWeightCompanionPositiveTorusJoin .E6 K := by
  obtain ⟨p, hp, _⟩ := e6PositiveTorusJoin_existsUnique K ⟨g, hg⟩
  change p.1.val * p.2.val = g at hp
  rw [← hp, map_mul]
  change companionTwist F K p.1.val * companionTwist F K p.2.val ∈
    selectedWeightCompanionPositiveSubgroup .E6 K ⊔
      selectedWeightCompanionTorusSubgroup .E6 K
  exact Subgroup.mul_mem_sup
    (e6PositiveSubgroup_twist_mem K F p.1.val p.1.property)
    (e6TorusSubgroup_twist_mem F K p.2.val p.2.property)

/-- Fixedness of a U*T product forces each entire factor to be fixed.
The proof compares its two factorizations using the inherited uniqueness. -/
theorem e6PositiveTorusProduct_fixed_iff
    (u : selectedWeightCompanionPositiveSubgroup .E6 K)
    (t : selectedWeightCompanionTorusSubgroup .E6 K) :
    u.val * t.val ∈ companionFixedSubgroup F K ↔
      u.val ∈ companionFixedSubgroup F K ∧ t.val ∈ companionFixedSubgroup F K := by
  constructor
  · intro hfixed
    change companionTwist F K (u.val * t.val) = u.val * t.val at hfixed
    let u' : selectedWeightCompanionPositiveSubgroup .E6 K :=
      ⟨companionTwist F K u.val, e6PositiveSubgroup_twist_mem K F u.val u.property⟩
    let t' : selectedWeightCompanionTorusSubgroup .E6 K :=
      ⟨companionTwist F K t.val, e6TorusSubgroup_twist_mem F K t.val t.property⟩
    have hprod : u'.val * t'.val = u.val * t.val :=
      (map_mul (companionTwist F K) u.val t.val).symm.trans hfixed
    have hmem : u.val * t.val ∈ selectedWeightCompanionPositiveTorusJoin .E6 K :=
      Subgroup.mul_mem_sup u.property t.property
    obtain ⟨p, _, hunique⟩ := e6PositiveTorusJoin_existsUnique K ⟨u.val * t.val, hmem⟩
    have he : (u', t') = (u, t) :=
      (hunique (u', t') hprod).trans (hunique (u, t) rfl).symm
    constructor
    · change companionTwist F K u.val = u.val
      exact congrArg
        (fun q : selectedWeightCompanionPositiveSubgroup .E6 K ×
          selectedWeightCompanionTorusSubgroup .E6 K => q.1.val) he
    · change companionTwist F K t.val = t.val
      exact congrArg
        (fun q : selectedWeightCompanionPositiveSubgroup .E6 K ×
          selectedWeightCompanionTorusSubgroup .E6 K => q.2.val) he
  · rintro ⟨hu, ht⟩
    exact (companionFixedSubgroup F K).mul_mem hu ht

/-- The literal intersection of the inherited B with the actual fixed group. -/
def companionFixedBorel : Subgroup (SelectedWeightCompanion .E6 K) :=
  selectedWeightCompanionPositiveTorusJoin .E6 K ⊓ companionFixedSubgroup F K

theorem mem_companionFixedBorel_iff (g : SelectedWeightCompanion .E6 K) :
    g ∈ companionFixedBorel F K ↔
      g ∈ selectedWeightCompanionPositiveTorusJoin .E6 K ∧ companionTwist F K g = g :=
  Iff.rfl

theorem companionPositiveFixed_le_fixedBorel :
    companionPositiveFixedSubgroup F K ≤ companionFixedBorel F K := by
  intro g hg
  exact ⟨(show selectedWeightCompanionPositiveSubgroup .E6 K ≤
    selectedWeightCompanionPositiveTorusJoin .E6 K from le_sup_left) hg.1, hg.2⟩

theorem companionFixedTorus_le_fixedBorel :
    companionFixedTorus F K ≤ companionFixedBorel F K := by
  intro g hg
  exact ⟨(show selectedWeightCompanionTorusSubgroup .E6 K ≤
    selectedWeightCompanionPositiveTorusJoin .E6 K from le_sup_right) hg.1, hg.2⟩

/-- This equality follows from the fixed-component theorem; it is not a
general interchange of fixed points and subgroup joins. -/
theorem companionFixedBorel_eq_sup :
    companionFixedBorel F K =
      companionPositiveFixedSubgroup F K ⊔ companionFixedTorus F K := by
  apply le_antisymm
  · intro g hg
    obtain ⟨p, hp, _⟩ := e6PositiveTorusJoin_existsUnique K ⟨g, hg.1⟩
    change p.1.val * p.2.val = g at hp
    have hfixed : p.1.val * p.2.val ∈ companionFixedSubgroup F K := by
      rw [hp]
      exact hg.2
    have hf := (e6PositiveTorusProduct_fixed_iff F K p.1 p.2).mp hfixed
    rw [← hp]
    exact Subgroup.mul_mem_sup
      (show p.1.val ∈ companionPositiveFixedSubgroup F K from ⟨p.1.property, hf.1⟩)
      (show p.2.val ∈ companionFixedTorus F K from ⟨p.2.property, hf.2⟩)
  · exact sup_le (companionPositiveFixed_le_fixedBorel F K)
      (companionFixedTorus_le_fixedBorel F K)

/-- Disjointness passes to the actual fixed subgroups. -/
theorem companionPositiveFixed_disjoint_fixedTorus :
    Disjoint (companionPositiveFixedSubgroup F K) (companionFixedTorus F K) := by
  apply Subgroup.disjoint_def.mpr
  intro g hu ht
  exact Subgroup.disjoint_def.mp (e6Positive_disjoint_torus K) hu.1 ht.1

/-- The fixed torus normalizes the full positive fixed subgroup. -/
theorem companionFixedTorus_le_positiveFixedNormalizer :
    companionFixedTorus F K ≤ Subgroup.normalizer (companionPositiveFixedSubgroup F K) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro t ht u hu
  constructor
  · exact (Subgroup.le_normalizer_iff.mp (e6Torus_le_positiveNormalizer K)) t ht.1 u hu.1
  · exact (companionFixedSubgroup F K).mul_mem
      ((companionFixedSubgroup F K).mul_mem ht.2 hu.2)
      ((companionFixedSubgroup F K).inv_mem ht.2)

theorem companionPositiveFixed_normal_in_fixedBorel :
    ((companionPositiveFixedSubgroup F K).subgroupOf (companionFixedBorel F K)).Normal := by
  rw [companionFixedBorel_eq_sup F K]
  exact Atlas.GroupTheory.normalizerJoin_normal _ _
    (companionFixedTorus_le_positiveFixedNormalizer F K)

/-- Conjugation by the actual fixed torus on the actual positive fixed subgroup. -/
def companionPositiveFixedTorusAction :
    companionFixedTorus F K →* MulAut (companionPositiveFixedSubgroup F K) :=
  (companionPositiveFixedSubgroup F K).normalizerMonoidHom.comp
    (Subgroup.inclusion (companionFixedTorus_le_positiveFixedNormalizer F K))

/-- The internal semidirect product maps by actual multiplication into B ∩ H. -/
def companionFixedBorelMulEquiv :
    companionPositiveFixedSubgroup F K ⋊[companionPositiveFixedTorusAction F K]
      companionFixedTorus F K ≃* companionFixedBorel F K :=
  (Atlas.GroupTheory.normalizerJoinMulEquiv
    (companionPositiveFixedSubgroup F K) (companionFixedTorus F K)
    (companionFixedTorus_le_positiveFixedNormalizer F K)
    (companionPositiveFixed_disjoint_fixedTorus F K)).trans
      (MulEquiv.subgroupCongr (companionFixedBorel_eq_sup F K).symm)

@[simp] theorem companionFixedBorelMulEquiv_val
    (x : companionPositiveFixedSubgroup F K ⋊[companionPositiveFixedTorusAction F K]
      companionFixedTorus F K) :
    (companionFixedBorelMulEquiv F K x).val = x.left.val * x.right.val := rfl

/-- Every element of the literal fixed Borel has a unique U^twist*T^twist expression. -/
theorem companionFixedBorel_existsUnique (g : companionFixedBorel F K) :
    ∃! p : companionPositiveFixedSubgroup F K × companionFixedTorus F K,
      p.1.val * p.2.val = g.val := by
  have hg : g.val ∈ companionPositiveFixedSubgroup F K ⊔ companionFixedTorus F K := by
    rw [← companionFixedBorel_eq_sup F K]
    exact g.property
  exact Atlas.GroupTheory.normalizerJoin_existsUnique
    (companionPositiveFixedSubgroup F K) (companionFixedTorus F K)
    (companionFixedTorus_le_positiveFixedNormalizer F K)
    (companionPositiveFixed_disjoint_fixedTorus F K) ⟨g.val, hg⟩

/-- The underlying set equivalence records the two whole factors. -/
def companionFixedBorelEquiv :
    (companionPositiveFixedSubgroup F K × companionFixedTorus F K) ≃
      companionFixedBorel F K :=
  (SemidirectProduct.equivProd (φ := companionPositiveFixedTorusAction F K)).symm.trans
    (companionFixedBorelMulEquiv F K).toEquiv

@[simp] theorem companionFixedBorelEquiv_val
    (p : companionPositiveFixedSubgroup F K × companionFixedTorus F K) :
    (companionFixedBorelEquiv F K p).val = p.1.val * p.2.val := rfl

/-- Count the actual fixed Borel using only the two fixed-factor counts. -/
theorem companionFixedBorel_card (hdeg : Module.finrank F K = 2) :
    Nat.card (companionFixedBorel F K) =
      Nat.card F ^ 36 * (Nat.card F - 1) ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
  calc
    _ = Nat.card (companionPositiveFixedSubgroup F K × companionFixedTorus F K) :=
      (Nat.card_congr (companionFixedBorelEquiv F K)).symm
    _ = Nat.card (companionPositiveFixedSubgroup F K) * Nat.card (companionFixedTorus F K) :=
      Nat.card_prod _ _
    _ = Nat.card F ^ 36 * (Nat.card F - 1) ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
      rw [companionPositiveFixedSubgroup_card K F hdeg, companionFixedTorus_card F K hdeg,
        mul_assoc]

end Atlas.Chevalley.TwistedE6
