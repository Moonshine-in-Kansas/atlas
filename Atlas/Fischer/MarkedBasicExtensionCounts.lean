import Atlas.Fischer.MarkedBasicExtensions
import Atlas.Fischer.WittParameters
import Atlas.Fischer.DuadWeightCounts

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

def duadReplication (S : Finset Omega) : ℕ := by
  classical
  exact ((Finset.univ : Finset Omega).powersetCard 2 |>.filter (S ⊆ ·)).card

theorem duadReplication_card (S : Finset Omega) :
    Nat.card {p : RootDuad // S ⊆ p.val} = duadReplication S := by
  classical
  let e : {p : RootDuad // S ⊆ p.val} ≃
      {p : Finset Omega // p ∈ (Finset.univ.powersetCard 2).filter (S ⊆ ·)} :=
    { toFun := fun p => ⟨p.val.val, by simp [p.val.property, p.property]⟩
      invFun := fun p => ⟨⟨p.val, (Finset.mem_powersetCard.mp (Finset.mem_filter.mp p.property).1).2⟩,
        (Finset.mem_filter.mp p.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

theorem duadReplication_small (S : Finset Omega) (hS : S.card ≤ 2) :
    duadReplication S = (24 - S.card).choose (2 - S.card) := by
  classical
  rw [duadReplication, Finset.card_filter_powersetCard_subset S Finset.univ 2
    (Finset.subset_univ S) hS]
  rfl

theorem duadReplication_large (S : Finset Omega) (hS : 2 < S.card) :
    duadReplication S = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
  have hn := (Finset.mem_powersetCard.mp hp).2
  have hh := Finset.card_le_card hs
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The marked-basic common-extension count, independently of group homogeneity. -/
theorem markedBasicExtension_card_formula (S : Finset Omega) :
    Nat.card (MarkedBasicExtension S) =
      (24 - S.card) + 32 * octadReplication S + 1024 * duadReplication S := by
  classical
  have hb : Nat.card {i : Omega // i ∉ S} = 24 - S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [Fintype.card_subtype, Omega, HexIndex]
  have ho (O : {O : Octad // S ⊆ O.val}) : Nat.card (OctadicCharacter O.val) = 32 :=
    octadCharacters_card O.val
  have hd (p : {p : RootDuad // S ⊆ p.val}) :
      Nat.card (Module.Dual Bit (duadShortenedCode p.val.val)) = 1024 :=
    duadCharacters_card p.val.val p.val.property
  have hO : Fintype.card {O : Octad // S ⊆ O.val} = octadReplication S := by
    rw [← Nat.card_eq_fintype_card]
    unfold octadReplication
    convert octad_predicate_card (fun O : Finset Omega => S ⊆ O) using 1
    congr 1
    ext O
    simp only [Finset.mem_filter]
  have hP : Fintype.card {p : RootDuad // S ⊆ p.val} = duadReplication S := by
    rw [← Nat.card_eq_fintype_card, duadReplication_card]
  rw [Nat.card_congr (markedBasicExtensionEquiv S), Nat.card_sum, Nat.card_sum,
    Nat.card_sigma, Nat.card_sigma, hb]
  simp only [ho, hd, Finset.sum_const, Finset.card_univ, smul_eq_mul, hO, hP]
  omega

end Atlas.Fischer
