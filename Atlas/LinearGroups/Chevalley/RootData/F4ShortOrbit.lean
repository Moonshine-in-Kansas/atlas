import Atlas.LinearGroups.Chevalley.RootData.F4
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords
import Mathlib.Data.Fin.VecNotation

/-! The actual24-point short-root orbit of F4, with finite local distance
certificates. Only roots and four simple reflections are tabulated; no Weyl
group enumeration or older F4 group order is used. -/
noncomputable section
namespace Atlas.Chevalley.F4ShortOrbit
open Classical RootData F4Data

abbrev W := pairing.weylGroupToPerm.range
def label (c : Fin 24) : F4Data.Root := ⟨c.val + 24, by omega⟩
def seed : F4Data.Root := label 0

theorem label_injective : Function.Injective label := by
  intro c d h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change c.val + 24 = d.val + 24 at hv
  omega

/-- The restriction of the four actual simple reflections to the short labels. -/
def step : Fin 4 → Fin 24 → Fin 24 :=
  ![![0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23],
    ![0,1,2,3,6,7,4,5,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23],
    ![0,1,2,3,4,5,7,6,9,8,11,10,13,12,15,14,17,16,19,18,21,20,23,22],
    ![8,23,11,20,13,18,14,17,0,9,10,2,12,4,6,16,15,7,5,19,3,21,22,1]]

theorem reflection_label (i : Fin 4) (c : Fin 24) :
    pairing.reflectionPerm (baseIndexEquiv i).val (label c) = label (step i c) := by
  change F4Table.reflectionIndex (F4Table.simpleIndex i) (label c) = _
  exact (show ∀ i : Fin 4, ∀ c : Fin 24,
    F4Table.reflectionIndex (F4Table.simpleIndex i) (label c) = label (step i c) by
      decide +kernel) i c

/-- Distances from the positive first axis. Equal distances retain distinct labels. -/
def distance : Fin 24 → ℕ :=
  ![0,15,5,10,6,9,7,8,1,2,3,4,4,5,6,7,8,9,10,11,11,12,13,14]

theorem distance_step_le : ∀ i : Fin 4, ∀ c : Fin 24,
    distance (step i c) ≤ distance c + 1 := by decide +kernel

theorem distance_eq_zero_iff : ∀ c : Fin 24, distance c = 0 ↔ c = 0 := by
  decide +kernel

theorem exists_predecessor : ∀ c : Fin 24, 0 < distance c →
    ∃ d : Fin 24, ∃ i : Fin 4,
      distance d + 1 = distance c ∧ step i d = c := by decide +kernel

def word : List base.support → Fin 24 → Fin 24
  | [], c => c
  | i :: l, c => step (baseIndexEquiv.symm i) (word l c)

theorem word_label (l : List base.support) (c : Fin 24) :
    simpleReflectionWord pairing base l (label c) = label (word l c) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
    change pairing.reflectionPerm (baseIndexEquiv k).val
      (simpleReflectionWord pairing base l (label c)) = _
    rw [ih, reflection_label]
    simp only [word, Equiv.symm_apply_apply]

theorem distance_word_le (l : List base.support) (c : Fin 24) :
    distance (word l c) ≤ distance c + l.length := by
  induction l with
  | nil => simp only [word, List.length_nil, add_zero, le_refl]
  | cons i l ih =>
    have hs := distance_step_le (baseIndexEquiv.symm i) (word l c)
    change distance (step (baseIndexEquiv.symm i) (word l c)) ≤ _
    simp only [List.length_cons]
    omega

theorem exists_distance_word (c : Fin 24) :
    ∃ l : List base.support, l.length = distance c ∧ word l 0 = c := by
  have aux : ∀ k : ℕ, ∀ c : Fin 24, distance c = k →
      ∃ l : List base.support, l.length = distance c ∧ word l 0 = c := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro c hc
      by_cases hk : k = 0
      · have hz := (distance_eq_zero_iff c).mp (hc.trans hk)
        subst c
        exact ⟨[], rfl, rfl⟩
      · obtain ⟨d, i, hd, hs⟩ := exists_predecessor c (by omega)
        obtain ⟨l, hlen, hw⟩ := ih (distance d) (by omega) d rfl
        refine ⟨baseIndexEquiv i :: l, ?_, ?_⟩
        · simpa only [List.length_cons, hlen] using hd
        · simpa only [word, Equiv.symm_apply_apply, hw] using hs
  exact aux (distance c) c rfl

theorem image_seed_label (w : W) : ∃ c : Fin 24, w.val seed = label c := by
  obtain ⟨l, _hlen, hl⟩ := rootWeylLength_spec pairing base w
  exact ⟨word l 0, by simpa only [hl, seed] using word_label l 0⟩

theorem distance_le_rootWeylLength (w : W) (c : Fin 24)
    (hc : w.val seed = label c) : distance c ≤ rootWeylLength pairing base w := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec pairing base w
  have he : label (word l 0) = label c := by
    rw [← word_label, hl]
    exact hc
  have hd := distance_word_le l 0
  have hz : distance (0 : Fin 24) = 0 := rfl
  simpa only [label_injective he, hz, zero_add, hlen] using hd

theorem exists_shortest_seed_word (c : Fin 24) :
    ∃ l : List base.support, IsReducedRootWord pairing base l ∧
      l.length = distance c ∧ (rootWeylWord pairing base l).val seed = label c := by
  obtain ⟨l, hlen, hw⟩ := exists_distance_word c
  have hc : (rootWeylWord pairing base l).val seed = label c := by
    simpa only [rootWeylWord_val, seed, hw] using word_label l 0
  refine ⟨l, ?_, hlen, hc⟩
  change rootWeylLength pairing base (rootWeylWord pairing base l) = l.length
  apply Nat.le_antisymm (rootWeylWord_length_le pairing base l)
  rw [hlen]
  exact distance_le_rootWeylLength _ c hc

def shortOrbitEquiv : Fin 24 ≃ {β : F4Data.Root // ∃ w : W, w.val seed = β} :=
  Equiv.ofBijective
    (fun c => ⟨label c, by
      obtain ⟨l, _hr, _hlen, hc⟩ := exists_shortest_seed_word c
      exact ⟨rootWeylWord pairing base l, hc⟩⟩)
    ⟨by intro c d h; exact label_injective (congrArg Subtype.val h), by
      rintro ⟨β, w, hw⟩
      obtain ⟨c, hc⟩ := image_seed_label w
      exact ⟨c, Subtype.ext (hc.symm.trans hw)⟩⟩

theorem shortOrbit_card : Nat.card {β : F4Data.Root // ∃ w : W, w.val seed = β} = 24 := by
  rw [← Nat.card_congr shortOrbitEquiv]
  simp

end Atlas.Chevalley.F4ShortOrbit
