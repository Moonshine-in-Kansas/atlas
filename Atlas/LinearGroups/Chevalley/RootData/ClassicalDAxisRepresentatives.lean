import Atlas.LinearGroups.Chevalley.RootData.ClassicalDAxisDistance

/-! Explicit shortest paths in the D signed-coordinate orbit, including D₂.
The paths use only actual simple reflections: ordinary adjacent swaps and the
terminal swap changing both signs. These are shortest actual Weyl words; the
right-parabolic representative identification is a separate next step. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDAxis
open Classical ClassicalData RootData

theorem distance_eq_zero_iff (n : ℕ) (c : Fin (n + 2) × Bool) :
    distance n c = 0 ↔ c = (0, true) := by
  rcases c with ⟨k, b⟩
  have hk := k.isLt
  cases b
  · simp only [distance, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq,
      and_false, iff_false]
    omega
  · change k.val = 0 ↔ (k, true) = (0, true)
    constructor
    · intro hk0
      exact congrArg (fun i : Fin (n + 2) => (i, true)) (Fin.ext hk0)
    · intro he
      exact congrArg (fun d : Fin (n + 2) × Bool => d.1.val) he

/-- Each noninitial signed coordinate has an explicit adjacent predecessor.
At the fork the positive and negative last coordinates use different simple
reflections, so equal distances do not identify their labels. -/
theorem exists_predecessor (n : ℕ) (c : Fin (n + 2) × Bool)
    (hc : 0 < distance n c) :
    ∃ d : Fin (n + 2) × Bool, ∃ i : Fin (n + 2),
      distance n d + 1 = distance n c ∧ step n i d = c := by
  rcases c with ⟨k, b⟩
  have hkBound := k.isLt
  cases b with
  | true =>
    have hk : 0 < k.val := by simpa only [distance, Bool.true_eq, ↓reduceIte] using hc
    let i : Fin (n + 2) := ⟨k.val - 1, by omega⟩
    have hi : i.val ≠ n + 1 := by dsimp only [i]; omega
    refine ⟨(i, true), i, ?_, ?_⟩
    · simp only [distance, ↓reduceIte]
      dsimp only [i]
      omega
    · simp only [step, hi, dite_false, ite_true]
      apply Prod.ext
      · apply Fin.ext
        dsimp only [i]
        omega
      · rfl
  | false =>
    by_cases hlast : k.val = n + 1
    · let p : Fin (n + 2) := ⟨n, by omega⟩
      let q : Fin (n + 2) := ⟨n + 1, by omega⟩
      refine ⟨(p, true), q, ?_, ?_⟩
      · simp only [distance, Bool.false_eq_true, ↓reduceIte]
        dsimp only [p]
        omega
      · simp only [step, p, q, dite_true, ite_true, Bool.not_true]
        apply Prod.ext
        · exact Fin.ext hlast.symm
        · rfl
    · let d : Fin (n + 2) := ⟨k.val + 1, by omega⟩
      have hdk : d ≠ k := by
        intro he
        have hh := congrArg Fin.val he
        dsimp only [d] at hh
        omega
      refine ⟨(d, false), k, ?_, ?_⟩
      · simp only [distance, Bool.false_eq_true, ↓reduceIte]
        dsimp only [d]
        omega
      · simp [step, hlast, hdk, d]

theorem word_append (n : ℕ) (l r : List (baseD n).support)
    (c : Fin (n + 2) × Bool) : word n (l ++ r) c = word n r (word n l c) := by
  induction l generalizing c with
  | nil => rfl
  | cons i l ih =>
    simpa only [List.cons_append, word] using
      (ih (step n ((baseDIndexEquiv n).symm i) c))

/-- A concrete sequence of actual simple nodes reaches each label with exactly
its displayed distance. This includes four D₂ labels of lengths 0,1,1,2. -/
theorem exists_distance_word (n : ℕ) (c : Fin (n + 2) × Bool) :
    ∃ l : List (baseD n).support,
      l.length = distance n c ∧ word n l (0, true) = c := by
  have aux : ∀ k : ℕ, ∀ c : Fin (n + 2) × Bool, distance n c = k →
      ∃ l : List (baseD n).support,
        l.length = distance n c ∧ word n l (0, true) = c := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro c hdist
      by_cases hk : k = 0
      · have hc := (distance_eq_zero_iff n c).mp (hdist.trans hk)
        subst c
        exact ⟨[], by simp [distance], rfl⟩
      · obtain ⟨d, i, hd, hs⟩ := exists_predecessor n c (by omega)
        obtain ⟨l, hlen, hw⟩ := ih (distance n d) (by omega) d rfl
        refine ⟨l ++ [baseDIndexEquiv n i], ?_, ?_⟩
        · simpa only [List.length_append, List.length_singleton, hlen] using hd
        · simpa only [word_append, hw, word, Equiv.symm_apply_apply] using hs
  exact aux (distance n c) c rfl

/-- The explicit path words are reduced for the actual root-permutation
length. No abstract presentation, stabilizer order or parabolic count enters. -/
theorem exists_reduced_coordinate_word (n : ℕ) (c : Fin (n + 2) × Bool) :
    ∃ l : List (baseD n).support,
      IsReducedRootWord (pairingD (n + 2)) (baseD n) l ∧
      l.length = distance n c ∧
      ∀ β : DRoot (n + 2),
        ((rootWeylWord (pairingD (n + 2)) (baseD n) l).val β).val 0 =
          coordinate n c β := by
  obtain ⟨l, hlen, hw⟩ := exists_distance_word n c
  have hcoord : ∀ β : DRoot (n + 2),
      ((rootWeylWord (pairingD (n + 2)) (baseD n) l).val β).val 0 =
        coordinate n c β := by
    intro β
    have he := coordinate_word n l (0, true) β
    simpa only [rootWeylWord_val, hw, coordinate, Integral.Minuscule.TypeD.sign,
      Bool.true_eq, ↓reduceIte, one_mul] using he
  refine ⟨l, ?_, hlen, hcoord⟩
  change rootWeylLength (pairingD (n + 2)) (baseD n)
    (rootWeylWord (pairingD (n + 2)) (baseD n) l) = l.length
  apply Nat.le_antisymm (rootWeylWord_length_le _ _ l)
  rw [hlen]
  exact distance_le_rootWeylLength n _ c hcoord

end Atlas.Chevalley.ClassicalDAxis
