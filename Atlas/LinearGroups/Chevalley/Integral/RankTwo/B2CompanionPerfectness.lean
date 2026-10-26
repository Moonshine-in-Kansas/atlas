import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionDoubleEdge
import Atlas.LinearGroups.Chevalley.WeightCompanionCrossTorus
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionPerfectness
import Atlas.GroupTheory.DoubleEdgeNormalPropagation

/-! Perfectness of the actual selected B2 companion. Cross-torus scaling
first supplies both short-root families in odd characteristic. The actual
positive and negative mixed words separately supply the long-root families.
The adjoint projection and the B2/C2 adjoint comparison are not used. -/

noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo.B2Companion
open Group ClassicalData
open scoped commutatorElement

private abbrev B2 : RootType := .B 2 (by decide)
local instance b2CompanionRootDecidableEq : DecidableEq (BRoot 2) :=
  Classical.decEq _
local instance b2CompanionBaseDecidableEq : DecidableEq (baseB 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseB 1).support})
local instance b2CompanionRankNeZero : NeZero B2.rank := ⟨by decide⟩

private theorem short_long_cartan :
    (rootDatum B2).base.cartanMatrix ((rootDatum B2).indexEquiv 1)
      ((rootDatum B2).indexEquiv 0) = -1 := by
  change (baseB 1).cartanMatrix (baseBIndexEquiv 1 1) (baseBIndexEquiv 1 0) = -1
  rw [baseB_cartan]
  decide

private theorem long_short_cartan :
    (rootDatum B2).base.cartanMatrix ((rootDatum B2).indexEquiv 0)
      ((rootDatum B2).indexEquiv 1) = -2 := by
  change (baseB 1).cartanMatrix (baseBIndexEquiv 1 0) (baseBIndexEquiv 1 1) = -2
  rw [baseB_cartan]
  decide

private theorem short_cartan_odd :
    Odd ((rootDatum B2).base.cartanMatrix ((rootDatum B2).indexEquiv 1)
      ((rootDatum B2).indexEquiv 0)) := by
  rw [short_long_cartan]
  decide

variable (K : Type*) [Field K]

private theorem Xshort_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    selectedWeightCompanionX B2 K 1 t ∈
      commutator (SelectedWeightCompanion B2 K) :=
  weightCompanionX_mem_commutator_of_odd_cartan (rootDatum B2).pairing
    (rootDatum B2).base (selectedWeightOrbits B2) (selectedWeightOrbits_closed B2)
    (selectedWeightOrbits_minuscule B2) K hchar
    ((rootDatum B2).indexEquiv 1) ((rootDatum B2).indexEquiv 0) short_cartan_odd t

private theorem Yshort_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    selectedWeightCompanionY B2 K 1 t ∈
      commutator (SelectedWeightCompanion B2 K) :=
  weightCompanionY_mem_commutator_of_odd_cartan (rootDatum B2).pairing
    (rootDatum B2).base (selectedWeightOrbits B2) (selectedWeightOrbits_closed B2)
    (selectedWeightOrbits_minuscule B2) K hchar
    ((rootDatum B2).indexEquiv 1) ((rootDatum B2).indexEquiv 0) short_cartan_odd t

private theorem Xlong_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    selectedWeightCompanionX B2 K 0 t ∈
      commutator (SelectedWeightCompanion B2 K) := by
  let W (k : Fin B2.rank) := selectedWeightCompanionX B2 K k 1 *
    selectedWeightCompanionY B2 K k (-1) * selectedWeightCompanionX B2 K k 1
  exact Atlas.GroupTheory.long_family_mem_normal_of_short_of_mixed_relation
    (commutator (SelectedWeightCompanion B2 K))
    (selectedWeightCompanionX B2 K 1) (selectedWeightCompanionX B2 K 0)
    (W 1) (W 0)
    (fun s u => selectedWeightCompanionX_b2_commutator_eq_weyl_product
      B2 K 1 0 (by decide) short_long_cartan long_short_cartan s u)
    (Xshort_mem_commutator K hchar) t

private theorem Ylong_mem_commutator (hchar : (-1 : K) ≠ 1) (t : K) :
    selectedWeightCompanionY B2 K 0 t ∈
      commutator (SelectedWeightCompanion B2 K) := by
  let V (k : Fin B2.rank) := selectedWeightCompanionY B2 K k 1 *
    selectedWeightCompanionX B2 K k (-1) * selectedWeightCompanionY B2 K k 1
  exact Atlas.GroupTheory.long_family_mem_normal_of_short_of_mixed_relation
    (commutator (SelectedWeightCompanion B2 K))
    (selectedWeightCompanionY B2 K 1) (selectedWeightCompanionY B2 K 0)
    (V 1) (V 0)
    (fun s u => selectedWeightCompanionY_b2_commutator_eq_negative_weyl_product
      B2 K 1 0 (by decide) short_long_cartan long_short_cartan s u)
    (Yshort_mem_commutator K hchar) t

theorem isPerfect_of_neg_one_ne_one (hchar : (-1 : K) ≠ 1) :
    IsPerfect (SelectedWeightCompanion (.B 2 (by decide)) K) := by
  change IsPerfect (SelectedWeightCompanion B2 K)
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  apply weightCompanion_induction (rootDatum B2).pairing (rootDatum B2).base
    (selectedWeightOrbits B2) (selectedWeightOrbits_closed B2)
    (selectedWeightOrbits_minuscule B2) K ?_ ?_ (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g
  · intro i t
    obtain ⟨k, rfl⟩ := (rootDatum B2).indexEquiv.surjective i
    fin_cases k
    · exact Xlong_mem_commutator K hchar t
    · exact Xshort_mem_commutator K hchar t
  · intro i t
    obtain ⟨k, rfl⟩ := (rootDatum B2).indexEquiv.surjective i
    fin_cases k
    · exact Ylong_mem_commutator K hchar t
    · exact Yshort_mem_commutator K hchar t

end Atlas.Chevalley.Integral.RankTwo.B2Companion

namespace Atlas.Chevalley
open Group
variable (K : Type*) [Field K]

/-- Both root signs are handled inside the actual simultaneous representation. -/
theorem selectedWeightCompanion_B2_isPerfect_of_neg_one_ne_one
    (hchar : (-1 : K) ≠ 1) :
    IsPerfect (SelectedWeightCompanion (.B 2 (by decide)) K) :=
  Integral.RankTwo.B2Companion.isPerfect_of_neg_one_ne_one K hchar

/-- The ternary field is the only finite q>2 case not supplied by the
existing generic same-root torus argument. -/
theorem selectedWeightCompanion_B2_isPerfect_of_card_three [Fintype K]
    (hq : Fintype.card K = 3) :
    IsPerfect (SelectedWeightCompanion (.B 2 (by decide)) K) :=
  selectedWeightCompanion_B2_isPerfect_of_neg_one_ne_one K
    (neg_one_ne_one_of_card_three K hq)

/-- In characteristic two this uses only the previously checked q>3 torus
argument. No perfectness assertion is made for q=2. -/
theorem selectedWeightCompanion_B2_isPerfect_of_card_gt_two [Fintype K]
    (hq : 2 < Fintype.card K) :
    IsPerfect (SelectedWeightCompanion (.B 2 (by decide)) K) := by
  by_cases hlarge : 3 < Fintype.card K
  · exact selectedWeightCompanion_isPerfect_of_card_gt_three (.B 2 (by decide)) K hlarge
  · exact selectedWeightCompanion_B2_isPerfect_of_card_three K (by omega)

end Atlas.Chevalley
