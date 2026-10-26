import Atlas.LinearGroups.Chevalley.RootData.ClassicalDAxisRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionBraids
import Atlas.LinearGroups.Chevalley.RootData.RootWeylPoincare
import Atlas.GroupTheory.TwoInvolutionsBound

/-! The actual D₂ base: two orthogonal commuting simple reflections and four
signed coordinate paths of lengths 0,1,1,2. No old orthogonal-group order or
abstract Weyl-group recognition is used. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDParabolic
open Classical ClassicalData RootData

private abbrev WTwo := (pairingD 2).weylGroupToPerm.range
private def firstSimple : (baseD 0).support := baseDIndexEquiv 0 0
private def secondSimple : (baseD 0).support := baseDIndexEquiv 0 1

/-- The upper bound uses the existing generic commuting-involutions theorem,
applied to the literal orthogonal D₂ simple reflections. -/
theorem rootWeyl_card_D_two_le : Nat.card WTwo ≤ 4 := by
  let a := simpleWeylReflection (pairingD 2) (baseD 0) firstSimple
  let b := simpleWeylReflection (pairingD 2) (baseD 0) secondSimple
  have h01 : (baseD 0).cartanMatrix firstSimple secondSimple = 0 := by
    rw [firstSimple, secondSimple, baseD_cartan]
    decide
  have h10 : (baseD 0).cartanMatrix secondSimple firstSimple = 0 := by
    rw [firstSimple, secondSimple, baseD_cartan]
    decide
  have hab : a * b = b * a := by
    simpa only [rootWeylWord, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] using
      rootWeylWord_braid_two (pairingD 2) (baseD 0) firstSimple secondSimple h01 h10
  let H : Subgroup WTwo := Subgroup.closure ({a, b} : Set WTwo)
  have hs : ∀ i : (baseD 0).support,
      simpleWeylReflection (pairingD 2) (baseD 0) i ∈ H := by
    intro i
    obtain ⟨k, rfl⟩ := (baseDIndexEquiv 0).surjective i
    fin_cases k
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hword : ∀ l : List (baseD 0).support,
      rootWeylWord (pairingD 2) (baseD 0) l ∈ H := by
    intro l
    induction l with
    | nil => exact H.one_mem
    | cons i l ih =>
      change simpleWeylReflection (pairingD 2) (baseD 0) i *
        rootWeylWord (pairingD 2) (baseD 0) l ∈ H
      exact H.mul_mem (hs i) ih
  have hgen : H = ⊤ := by
    apply le_antisymm le_top
    intro w hw
    obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec (pairingD 2) (baseD 0) w
    have he : rootWeylWord (pairingD 2) (baseD 0) l = w := by
      apply Subtype.ext
      rw [rootWeylWord_val]
      exact hl
    rw [← he]
    exact hword l
  exact Atlas.card_le_four_of_two_commuting_involutions a b
    (simpleWeylReflection_mul_self (pairingD 2) (baseD 0) firstSimple)
    (simpleWeylReflection_mul_self (pairingD 2) (baseD 0) secondSimple) hab hgen

private def rankTwoWord (c : Fin 2 × Bool) : List (baseD 0).support :=
  (ClassicalDAxis.exists_reduced_coordinate_word 0 c).choose

private theorem rankTwoWord_spec (c : Fin 2 × Bool) :
    IsReducedRootWord (pairingD 2) (baseD 0) (rankTwoWord c) ∧
      (rankTwoWord c).length = ClassicalDAxis.distance 0 c ∧
      ∀ β : DRoot 2,
        ((rootWeylWord (pairingD 2) (baseD 0) (rankTwoWord c)).val β).val 0 =
          ClassicalDAxis.coordinate 0 c β :=
  (ClassicalDAxis.exists_reduced_coordinate_word 0 c).choose_spec

/-- Four distinct actual root-permutation elements, distinguished by their
first coordinate functions, rather than by their possibly equal lengths. -/
def rankTwoCoordinateMap (c : Fin 2 × Bool) : WTwo :=
  rootWeylWord (pairingD 2) (baseD 0) (rankTwoWord c)

theorem rankTwoCoordinateMap_injective : Function.Injective rankTwoCoordinateMap := by
  intro c d h
  apply ClassicalDAxis.coordinate_injective 0
  funext β
  calc
    ClassicalDAxis.coordinate 0 c β = ((rankTwoCoordinateMap c).val β).val 0 :=
      ((rankTwoWord_spec c).2.2 β).symm
    _ = ((rankTwoCoordinateMap d).val β).val 0 := by rw [h]
    _ = ClassicalDAxis.coordinate 0 d β := (rankTwoWord_spec d).2.2 β

theorem rankTwoCoordinateMap_bijective : Function.Bijective rankTwoCoordinateMap := by
  apply rankTwoCoordinateMap_injective.bijective_of_nat_card_le
  simpa only [Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] using rootWeyl_card_D_two_le

/-- An actual set equivalence, retaining both middle labels of length one. -/
def rankTwoCoordinateEquiv : (Fin 2 × Bool) ≃ WTwo :=
  Equiv.ofBijective rankTwoCoordinateMap rankTwoCoordinateMap_bijective

theorem rankTwoCoordinateEquiv_length (c : Fin 2 × Bool) :
    rootWeylLength (pairingD 2) (baseD 0) (rankTwoCoordinateEquiv c) =
      ClassicalDAxis.distance 0 c :=
  (rankTwoWord_spec c).1.trans (rankTwoWord_spec c).2.1

/-- The D₂ Poincare base is derived from the four actual elements and their
shortest lengths 0,1,1,2, for every natural evaluation parameter. -/
theorem rootWeylPoincareEval_D_two (q : ℕ) :
    rootWeylPoincareEval (pairingD 2) (baseD 0) q = (1 + q) ^ 2 := by
  letI : Fintype WTwo := Fintype.ofFinite _
  have hsum : rootWeylPoincareEval (pairingD 2) (baseD 0) q =
      ∑ c : Fin 2 × Bool,
        q ^ rootWeylLength (pairingD 2) (baseD 0) (rankTwoCoordinateEquiv c) := by
    exact (rankTwoCoordinateEquiv.sum_comp
      (fun w => q ^ rootWeylLength (pairingD 2) (baseD 0) w)).symm
  rw [hsum]
  simp only [rankTwoCoordinateEquiv_length]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ClassicalDAxis.distance, Bool.true_eq,
    Bool.false_eq_true, ↓reduceIte]
  norm_num [Fin.sum_univ_two]
  ring

end Atlas.Chevalley.ClassicalDParabolic
