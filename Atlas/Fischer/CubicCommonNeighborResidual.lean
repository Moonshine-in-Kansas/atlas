import Atlas.Fischer.CubicCommonNeighborProfiles

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

abbrev CubicResidualColumn (i j k : Fin 6) := {l : Fin 6 // l ≠ i ∧ l ≠ j ∧ l ≠ k}

theorem cubicResidualColumn_card (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (CubicResidualColumn i j k)=3 := by
  rw [Nat.card_eq_fintype_card]
  have he := Fintype.card_of_subtype ({i,j,k}ᶜ : Finset (Fin 6))
    (p := fun l => l ≠ i ∧ l ≠ j ∧ l ≠ k) (by intro l; simp)
  rw [he,Finset.card_compl,Fintype.card_fin]
  simp [hij,hik,hjk]

theorem cubicCommonNeighbor_two_completion (S : Finset (Fin 6)) (hS : S.card=2)
    (i : Fin 6) (hi : i ∈ S) : ∃ l,l ≠ i ∧ S={i,l} := by
  have he : (S.erase i).card=1 := by rw [Finset.card_erase_of_mem hi,hS]
  obtain ⟨l,hl⟩ := Finset.card_eq_one.mp he
  have hm : l ∈ S.erase i := by rw [hl]; simp
  refine ⟨l,(Finset.mem_erase.mp hm).1,?_⟩
  rw [← Finset.insert_erase hi,hl]

theorem cubicCommonNeighbor_four_completion (S : Finset (Fin 6)) (hS : S.card=4)
    (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S) :
    ∃ l : CubicResidualColumn i j k,S={i,j,k,l.val} := by
  have hsub : {i,j,k} ⊆ S := by simp [Finset.insert_subset_iff,hi,hj,hk]
  have hc : ({i,j,k} : Finset (Fin 6)).card=3 := by simp [hij,hik,hjk]
  have he : (S \ {i,j,k}).card=1 := by rw [Finset.card_sdiff_of_subset hsub,hS,hc]
  obtain ⟨l,hl⟩ := Finset.card_eq_one.mp he
  have hm : l ∈ S \ {i,j,k} := by rw [hl]; simp
  have hres : l ≠ i ∧ l ≠ j ∧ l ≠ k := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using (Finset.mem_sdiff.mp hm).2
  refine ⟨⟨l,hres⟩,?_⟩
  rw [← Finset.union_sdiff_of_subset hsub,hl]
  ext x
  simp

def cubicSourceCommonFourMap (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (l : CubicResidualColumn i j k) :
    CubicSourceCommonNeighbors i j k 4 :=
  ⟨.inl ⟨{i,l.val},Finset.card_pair (Ne.symm l.property.1)⟩,
    (cubicSourceCommonCondition_A i j k 4 _).mpr (Or.inr
      ⟨rfl,by simp,by simp [Ne.symm hij,Ne.symm l.property.2.1],by simp [Ne.symm hik,Ne.symm l.property.2.2]⟩)⟩

def cubicSourceCommonFourEquiv (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CubicResidualColumn i j k ≃ CubicSourceCommonNeighbors i j k 4 :=
  Equiv.ofBijective (cubicSourceCommonFourMap i j k hij hik) (by
    constructor
    · intro l m h
      have hs : ({i,l.val} : Finset (Fin 6))={i,m.val} := by
        exact congrArg (fun t : CountingSourceParameters =>
          match t with | .inl a => a.val | _ => ∅) (congrArg Subtype.val h)
      have hm : l.val ∈ ({i,m.val} : Finset (Fin 6)) := by rw [← hs]; simp
      apply Subtype.ext
      simpa [l.property.1] using hm
    · rintro ⟨a | (b | c),h⟩
      · rcases (cubicSourceCommonCondition_A i j k 4 a).mp h with ha | ha
        · omega
        · obtain ⟨l,hli,hl⟩ := cubicCommonNeighbor_two_completion a.val a.property i ha.2.1
          have hlj : l ≠ j := by intro he; subst l; apply ha.2.2.1; rw [hl]; simp
          have hlk : l ≠ k := by intro he; subst l; apply ha.2.2.2; rw [hl]; simp
          refine ⟨⟨l,hli,hlj,hlk⟩,?_⟩
          apply Subtype.ext
          exact congrArg Sum.inl (Subtype.ext hl.symm)
      · have hh := (cubicSourceCommonCondition_B i j k 4 b).mp h
        omega
      · have hh := (cubicSourceCommonCondition_C i j k 4 c hij hik hjk).mp h
        omega)

theorem cubicSourceCommonFour_card (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (CubicSourceCommonNeighbors i j k 4)=3 := by
  rw [← Nat.card_congr (cubicSourceCommonFourEquiv i j k hij hik hjk),cubicResidualColumn_card i j k hij hik hjk]

end Atlas.Fischer
