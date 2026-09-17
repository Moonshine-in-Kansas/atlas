import Atlas.Fischer.CubicCommonNeighborColumns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem cubicSourceCommonCondition_A (i j k : Fin 6) (u : ℕ) (t : CountingSourceTypeA) :
    cubicSourceCommonCondition i j k u (.inl t) ↔
      (u=0 ∧ i ∉ t.val ∧ j ∈ t.val ∧ k ∈ t.val) ∨
      (u=4 ∧ i ∈ t.val ∧ j ∉ t.val ∧ k ∉ t.val) := by
  unfold cubicSourceCommonCondition
  simp only [countingSourceColumn_card_A]
  by_cases hi : i ∈ t.val <;> by_cases hj : j ∈ t.val <;> by_cases hk : k ∈ t.val <;>
    simp [hi,hj,hk] <;> omega

theorem cubicSourceCommonCondition_B (i j k : Fin 6) (u : ℕ) (t : CountingSourceTypeB) :
    cubicSourceCommonCondition i j k u (.inr (.inl t)) ↔
      u=2 ∧ t.1.val.val i ≠ 0 ∧ t.1.val.val j ≠ 0 ∧ t.1.val.val k ≠ 0 := by
  unfold cubicSourceCommonCondition
  simp only [countingSourceColumn_card_B]
  by_cases hi : t.1.val.val i=0 <;> by_cases hj : t.1.val.val j=0 <;>
    by_cases hk : t.1.val.val k=0 <;> simp [hi,hj,hk] <;> omega

theorem cubicSourceCommonCondition_C (i j k : Fin 6) (u : ℕ) (t : CountingSourceTypeC)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cubicSourceCommonCondition i j k u (.inr (.inr t)) ↔ u=3 ∧ t.2=i := by
  unfold cubicSourceCommonCondition
  simp only [countingSourceColumn_card_C]
  by_cases hi : i=t.2 <;> by_cases hj : j=t.2 <;> by_cases hk : k=t.2 <;>
    simp_all <;> omega

theorem cubicSourceCommonCondition_levels (i j k : Fin 6) (u : ℕ)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : CubicSourceCommonNeighbors i j k u) : u=0 ∨ u=2 ∨ u=3 ∨ u=4 := by
  rcases t with ⟨a | (b | c),h⟩
  · rcases (cubicSourceCommonCondition_A i j k u a).mp h with h | h <;> omega
  · have hh := (cubicSourceCommonCondition_B i j k u b).mp h
    omega
  · have hh := (cubicSourceCommonCondition_C i j k u c hij hik hjk).mp h
    omega

def cubicSourceCommonZero (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CubicSourceCommonNeighbors i j k 0 :=
  ⟨.inl ⟨{j,k},Finset.card_pair hjk⟩,(cubicSourceCommonCondition_A i j k 0 _).mpr
    (Or.inl ⟨rfl,by simp [hij,hik],by simp,by simp⟩)⟩

theorem cubicSourceCommonZero_unique (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : CubicSourceCommonNeighbors i j k 0) : t=cubicSourceCommonZero i j k hij hik hjk := by
  apply Subtype.ext
  rcases t with ⟨a | (b | c),h⟩
  · rcases (cubicSourceCommonCondition_A i j k 0 a).mp h with ha | ha
    · have hs : {j,k} ⊆ a.val := Finset.insert_subset ha.2.2.1 (Finset.singleton_subset_iff.mpr ha.2.2.2)
      have he : a.val={j,k} := (Finset.eq_of_subset_of_card_le hs
        (by rw [a.property,Finset.card_pair hjk])).symm
      exact congrArg Sum.inl (Subtype.ext he)
    · omega
  · have hh := (cubicSourceCommonCondition_B i j k 0 b).mp h
    omega
  · have hh := (cubicSourceCommonCondition_C i j k 0 c hij hik hjk).mp h
    omega

theorem cubicSourceCommonZero_card (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (CubicSourceCommonNeighbors i j k 0)=1 := by
  letI : Unique (CubicSourceCommonNeighbors i j k 0) :=
    ⟨⟨cubicSourceCommonZero i j k hij hik hjk⟩,cubicSourceCommonZero_unique i j k hij hik hjk⟩
  exact Nat.card_unique

def cubicSourceCommonThreeEquiv (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    countingHexacode ≃ CubicSourceCommonNeighbors i j k 3 :=
  Equiv.ofBijective (fun h => ⟨.inr (.inr (h,i)),
    (cubicSourceCommonCondition_C i j k 3 (h,i) hij hik hjk).mpr ⟨rfl,rfl⟩⟩) (by
    constructor
    · intro a b h
      exact congrArg (fun t : CountingSourceParameters =>
        match t with | .inr (.inr c) => c.1 | _ => 0) (congrArg Subtype.val h)
    · rintro ⟨a | (b | c),h⟩
      · rcases (cubicSourceCommonCondition_A i j k 3 a).mp h with h | h <;> omega
      · have hh := (cubicSourceCommonCondition_B i j k 3 b).mp h
        omega
      · have hh := (cubicSourceCommonCondition_C i j k 3 c hij hik hjk).mp h
        refine ⟨c.1,?_⟩
        apply Subtype.ext
        exact congrArg (fun z : CountingSourceTypeC =>
          (Sum.inr (Sum.inr z) : CountingSourceParameters))
          (Prod.ext rfl hh.2.symm))

theorem cubicSourceCommonThree_card (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (CubicSourceCommonNeighbors i j k 3)=64 := by
  rw [← Nat.card_congr (cubicSourceCommonThreeEquiv i j k hij hik hjk),countingHexacode_card]

end Atlas.Fischer
