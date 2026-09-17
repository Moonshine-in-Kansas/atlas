import Atlas.Conway.OrthogonalPairSigns

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def OrthogonalFourClass (i j : Omega) :=
  {x : leech // x.val ∈ twoFourFamily 0 2 ∧ integerDot (minimumPairPlus i j).val x.val = 0}

theorem pairSign_four_orthogonal (i j : Omega) (hij : i ≠ j) (x : PairSignClass i j) :
    x.val.val ∈ twoFourFamily 0 2 ∧ integerDot (minimumPairPlus i j).val x.val.val = 0 := by
  rcases x.prop with he | he
  · rw [he]
    exact ⟨minimumPairMinus_four_mem i j hij,minimumPair_orthogonal i j hij⟩
  · rw [he]
    refine ⟨neg_minimumPairMinus_four_mem i j hij,?_⟩
    change integerDot (minimumPairPlus i j).val (-(minimumPairMinus i j).val) = 0
    have hn : ∀ u v : IntegerCoordinates, integerDot u (-v) = -integerDot u v := by
      intro u v
      simp [integerDot,Finset.sum_neg_distrib]
    rw [hn,minimumPair_orthogonal i j hij,neg_zero]

theorem pairSign_coordinate_ne_zero (i j : Omega) (hij : i ≠ j) (x : PairSignClass i j) :
    x.val.val i ≠ 0 := by
  rcases x.prop with he | he <;> rw [he]
  · norm_num [minimumPairMinus,coordinateVector,Pi.single_apply,hij]
  · change -((minimumPairMinus i j).val i) ≠ 0
    norm_num [minimumPairMinus,coordinateVector,Pi.single_apply,hij]

def orthogonalFourEquiv (i j : Omega) (hij : i ≠ j) :
    OrthogonalFourClass i j ≃ PairSignClass i j ⊕ DisjointFourClass {i,j} := by
  let p : leech → Prop := fun x => x = minimumPairMinus i j ∨ x = -minimumPairMinus i j
  let q : leech → Prop := fun x => x.val ∈ twoFourFamily 0 2 ∧ ∀ k ∈ ({i,j} : Finset Omega), x.val k = 0
  have hdis : Disjoint p q := Set.disjoint_left.mpr (by
    intro x hp hq
    exact pairSign_coordinate_ne_zero i j hij ⟨x,hp⟩ (hq.2 i (by simp)))
  have he (x : leech) :
      (x.val ∈ twoFourFamily 0 2 ∧ integerDot (minimumPairPlus i j).val x.val = 0) ↔ p x ∨ q x := by
    constructor
    · rintro ⟨hx,ho⟩
      rcases four_orthogonal_partition i j hij x hx ho with hp | hz
      · exact Or.inl hp
      · right
        refine ⟨hx,?_⟩
        intro k hk
        simp only [Finset.mem_insert,Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hz.1
        · exact hz.2
    · rintro (hp | hq)
      · exact pairSign_four_orthogonal i j hij ⟨x,hp⟩
      · refine ⟨hq.1,?_⟩
        rw [minimumPairPlus_dot,hq.2 i (by simp),hq.2 j (by simp)]
        norm_num
  exact (Equiv.subtypeEquivRight he).trans (subtypeOrEquiv p q hdis)

theorem orthogonalFourClass_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (OrthogonalFourClass i j) = 926 := by
  letI : Finite (PairSignClass i j) := Nat.finite_of_card_ne_zero (by
    rw [pairSignClass_card i j hij]; decide)
  letI : Finite (DisjointFourClass {i,j}) := Nat.finite_of_card_ne_zero (by
    rw [disjointFourPair_card i j hij]; decide)
  rw [Nat.card_congr (orthogonalFourEquiv i j hij),Nat.card_sum,
    pairSignClass_card i j hij,disjointFourPair_card i j hij]

end Atlas.Conway
