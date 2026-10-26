import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesD
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDAction
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionReducedWords

/-! Signed coordinate distances for the actual D simple reflections, including
D₂. The fork has two distinct labels at the same middle distance. No signed
permutation classification or Weyl-group order is used. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDAxis
open Classical ClassicalData RootData Integral.Minuscule.TypeD

/-- A coordinate function on actual D roots. -/
def coordinate (n : ℕ) (c : Fin (n + 2) × Bool) : DRoot (n + 2) → ℤ :=
  fun β => sign c.2 * β.val c.1

/-- Every nonterminal simple reflection swaps adjacent coordinates. The last
simple reflection swaps the last two coordinates and changes both signs. -/
def step (n : ℕ) (i : Fin (n + 2)) (c : Fin (n + 2) × Bool) :
    Fin (n + 2) × Bool :=
  if h : i.val = n + 1 then
    if c.1.val = n then (⟨n + 1, by omega⟩, !c.2)
    else if c.1.val = n + 1 then (⟨n, by omega⟩, !c.2) else c
  else if c.1 = i then (⟨i.val + 1, by omega⟩, c.2)
    else if c.1.val = i.val + 1 then (i, c.2) else c

/-- The literal integral root action agrees with this signed-coordinate step. -/
theorem coordinate_simple (n : ℕ) (i : Fin (n + 2))
    (c : Fin (n + 2) × Bool) (β : DRoot (n + 2)) :
    coordinate n c ((pairingD (n + 2)).reflectionPerm (simpleD n i) β) =
      coordinate n (step n i c) β := by
  change sign c.2 * reflect (simpleD n i) β.val c.1 = _
  by_cases hi : i.val = n + 1
  · simp only [simpleD, hi, dite_true]
    rw [reflect_long_coordinates]
    by_cases hp : c.1.val = n
    · have hep : c.1 = (⟨n, by omega⟩ : Fin (n + 2)) := Fin.ext hp
      cases hb : c.2 <;> simp [coordinate, step, hi, hep, sign, hb]
    · by_cases hq : c.1.val = n + 1
      · have heq : c.1 = (⟨n + 1, by omega⟩ : Fin (n + 2)) := Fin.ext hq
        cases hb : c.2 <;> simp [coordinate, step, hi, heq, sign, hb]
      · have hnep : c.1 ≠ (⟨n, by omega⟩ : Fin (n + 2)) :=
          fun he => hp (congrArg Fin.val he)
        have hneq : c.1 ≠ (⟨n + 1, by omega⟩ : Fin (n + 2)) :=
          fun he => hq (congrArg Fin.val he)
        simp [coordinate, step, hi, hp, hq, hnep, hneq]
  · simp only [simpleD, hi, dite_false]
    rw [reflect_long_coordinates]
    by_cases hci : c.1 = i
    · simp [coordinate, step, hi, hci]
    · by_cases hcj : c.1.val = i.val + 1
      · have he : c.1 = (⟨i.val + 1, by omega⟩ : Fin (n + 2)) := Fin.ext hcj
        have hnext : (⟨i.val + 1, by omega⟩ : Fin (n + 2)) ≠ i := by
          intro hh
          have hv := congrArg Fin.val hh
          change i.val + 1 = i.val at hv
          omega
        simp [coordinate, step, hi, he, hnext]
      · have he : c.1 ≠ (⟨i.val + 1, by omega⟩ : Fin (n + 2)) :=
          fun he => hcj (congrArg Fin.val he)
        simp [coordinate, step, hi, hci, hcj, he]

/-- Distance from the first positive coordinate. In rank r=n+2, the two
last-coordinate signs both have distance r−1. -/
def distance (n : ℕ) (c : Fin (n + 2) × Bool) : ℕ :=
  if c.2 then c.1.val else 2 * (n + 1) - c.1.val

/-- No actual simple reflection changes the distance by more than one. -/
theorem distance_step_le (n : ℕ) (i : Fin (n + 2)) (c : Fin (n + 2) × Bool) :
    distance n (step n i c) ≤ distance n c + 1 := by
  have hiBound := i.isLt
  have hcBound := c.1.isLt
  by_cases hi : i.val = n + 1
  · by_cases hp : c.1.val = n
    · cases hb : c.2 <;> simp [step, hi, hp, distance, hb] <;> omega
    · by_cases hq : c.1.val = n + 1
      · cases hb : c.2 <;> simp [step, hi, hq, distance, hb] <;> omega
      · simp [step, hi, hp, hq]
  · by_cases hci : c.1 = i
    · cases hb : c.2 <;> simp [step, hi, hci, distance, hb]
      all_goals omega
    · by_cases hcj : c.1.val = i.val + 1
      · cases hb : c.2 <;> simp [step, hi, hci, hcj, distance, hb] <;> omega
      · simp [step, hi, hci, hcj]

/-- Pullback of coordinates follows the word from left to right. -/
def word (n : ℕ) : List (baseD n).support → Fin (n + 2) × Bool → Fin (n + 2) × Bool
  | [], c => c
  | i :: l, c => word n l (step n ((baseDIndexEquiv n).symm i) c)

theorem coordinate_word (n : ℕ) (l : List (baseD n).support)
    (c : Fin (n + 2) × Bool) (β : DRoot (n + 2)) :
    coordinate n c (simpleReflectionWord (pairingD (n + 2)) (baseD n) l β) =
      coordinate n (word n l c) β := by
  induction l generalizing c with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨k, rfl⟩ := (baseDIndexEquiv n).surjective i
    change coordinate n c ((pairingD (n + 2)).reflectionPerm (simpleD n k)
      (simpleReflectionWord (pairingD (n + 2)) (baseD n) l β)) = _
    rw [coordinate_simple, ih]
    simp only [word, Equiv.symm_apply_apply]

theorem distance_word_le (n : ℕ) (l : List (baseD n).support)
    (c : Fin (n + 2) × Bool) :
    distance n (word n l c) ≤ distance n c + l.length := by
  induction l generalizing c with
  | nil => simp [word]
  | cons i l ih =>
    have h := ih (step n ((baseDIndexEquiv n).symm i) c)
    have hs := distance_step_le n ((baseDIndexEquiv n).symm i) c
    change distance n (word n l (step n ((baseDIndexEquiv n).symm i) c)) ≤ _
    simp only [List.length_cons]
    omega

/-- Already D₂ roots distinguish all signed coordinate functions. -/
theorem coordinate_injective (n : ℕ) : Function.Injective (coordinate n) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hki⟩ := exists_ne i
    have he := congrFun h (longRoot false i k (Ne.symm hki) 1 1 (Or.inl rfl) (Or.inl rfl))
    cases b <;> cases c <;>
      simp_all [coordinate, sign, longRoot, Ne.symm hki]
  · have hp := congrFun h (longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl))
    have hm := congrFun h (longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl))
    cases b <;> cases c <;>
      simp_all [coordinate, sign, longRoot, Ne.symm hij]

/-- The coordinate distance bounds the actual minimum simple-word length. -/
theorem distance_le_rootWeylLength (n : ℕ)
    (w : (pairingD (n + 2)).weylGroupToPerm.range) (c : Fin (n + 2) × Bool)
    (hc : ∀ β : DRoot (n + 2), (w.val β).val 0 = coordinate n c β) :
    distance n c ≤ rootWeylLength (pairingD (n + 2)) (baseD n) w := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec (pairingD (n + 2)) (baseD n) w
  have he : coordinate n (word n l (0, true)) = coordinate n c := by
    funext β
    rw [← coordinate_word, hl]
    simpa only [coordinate, sign, Bool.true_eq, ↓reduceIte, one_mul] using hc β
  have hlabel := coordinate_injective n he
  have hd := distance_word_le n l (0, true)
  simpa only [hlabel, distance, Bool.true_eq, ↓reduceIte, Fin.val_zero,
    zero_add, hlen] using hd

end Atlas.Chevalley.ClassicalDAxis
