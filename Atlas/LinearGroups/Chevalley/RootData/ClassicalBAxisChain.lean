import Atlas.LinearGroups.Chevalley.RootData.ClassicalBParabolicOrbit

/-! Exact action of the actual simple B reflections on signed coordinate
axes. Their orbit graph is the line e0,...,en,-en,...,-e0. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalBParabolic
open Classical ClassicalData RootData

def axisStep (n : ℕ) (i : Fin (n + 1)) (c : Fin (n + 1) × Bool) :
    Fin (n + 1) × Bool :=
  if h : i.val < n then
    (Equiv.swap i ⟨i.val + 1, by omega⟩ c.1, c.2)
  else (c.1, if c.1 = i then !c.2 else c.2)

private theorem reflect_difference_swap {r : ℕ} (i j : Fin r) (hij : i ≠ j)
    (x : Lattice r) (k : Fin r) :
    reflect (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) x k =
      x (Equiv.swap i j k) := by
  have hdot : dot (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)).val x =
      x i - x j := by
    simp [longRoot, dot_add_left, dot_single_left, sub_eq_add_neg]
  simp only [reflect]
  rw [long_scale, hdot, one_mul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, longRoot, Pi.add_apply]
  by_cases hki : k = i
  · subst k
    simp [Pi.single_apply, hij, Ne.symm hij, Equiv.swap_apply_def]
    <;> ring
  · by_cases hkj : k = j
    · subst k
      simp [Pi.single_apply, hij, Ne.symm hij, Equiv.swap_apply_def]
      <;> ring
    · simp [Pi.single_apply, hki, hkj, Equiv.swap_apply_def]

/-- This is the actual integral root-label action, not a supplied permutation model. -/
theorem simple_reflection_axis (n : ℕ) (i : Fin (n + 1)) (c : Fin (n + 1) × Bool) :
    (pairingB (n + 1)).reflectionPerm (simple n i).val (decodeShort c) =
      decodeShort (axisStep n i c) := by
  apply Subtype.ext
  funext k
  change reflect (simpleB n i) (decodeShort c).val k = (decodeShort (axisStep n i c)).val k
  by_cases hi : i.val < n
  · simp only [simpleB, hi, dite_true]
    rw [reflect_difference_swap]
    simp only [axisStep, hi, dite_true, decodeShort, shortRoot, Pi.single_apply]
    simp only [Equiv.swap_apply_eq_iff]
  · simp only [simpleB, hi, dite_false]
    rw [reflect_short]
    by_cases hci : c.1 = i
    · cases hb : c.2 <;> by_cases hk : k = i <;>
        simp [axisStep, hi, hci, decodeShort, shortRoot, Pi.single_apply, hb, hk]
    · by_cases hk : k = i
      · subst k
        simp [axisStep, hi, hci, decodeShort, shortRoot, Pi.single_apply, Ne.symm hci]
      · simp [axisStep, hi, hci, decodeShort, shortRoot, Pi.single_apply, hk]

/-- Distance from the first positive axis in the explicit signed-axis line. -/
def axisHeight (n : ℕ) (c : Fin (n + 1) × Bool) : ℕ :=
  if c.2 then c.1.val else 2 * n + 1 - c.1.val

theorem axisHeight_lt (n : ℕ) (c : Fin (n + 1) × Bool) :
    axisHeight n c < 2 * (n + 1) := by
  have hk := c.1.isLt
  unfold axisHeight
  split_ifs <;> omega

/-- A single actual simple reflection changes the orbit distance by at most one. -/
theorem axisHeight_step_le (n : ℕ) (i : Fin (n + 1)) (c : Fin (n + 1) × Bool) :
    axisHeight n (axisStep n i c) ≤ axisHeight n c + 1 := by
  have hiBound := i.isLt
  have hcBound := c.1.isLt
  by_cases hi : i.val < n
  · let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have hj : j.val = i.val + 1 := rfl
    by_cases hci : c.1 = i
    · have hij : i ≠ j := by intro h; have := congrArg Fin.val h; omega
      cases hb : c.2 <;>
        simp [axisStep, hi, axisHeight, hci, hb, j] <;> omega
    · by_cases hcj : c.1 = j
      · cases hb : c.2 <;>
          simp [axisStep, hi, axisHeight, hcj, hb, j] <;> omega
      · have hswap : Equiv.swap i j c.1 = c.1 := Equiv.swap_apply_of_ne_of_ne hci hcj
        simp only [axisStep, hi, dite_true]
        change axisHeight n (Equiv.swap i j c.1, c.2) ≤ _
        rw [hswap]
        change axisHeight n c ≤ axisHeight n c + 1
        omega
  · have hin : i.val = n := by omega
    by_cases hci : c.1 = i
    · cases hb : c.2 <;> simp [axisStep, hi, hci, axisHeight, hb, hin] <;> omega
    · simp [axisStep, hi, hci]

def axisWord (n : ℕ) : List (baseB n).support → Fin (n + 1) × Bool → Fin (n + 1) × Bool
  | [], c => c
  | i :: l, c => axisStep n ((baseBIndexEquiv n).symm i) (axisWord n l c)

theorem simpleReflectionWord_axis (n : ℕ) (l : List (baseB n).support)
    (c : Fin (n + 1) × Bool) :
    simpleReflectionWord (pairingB (n + 1)) (baseB n) l (decodeShort c) =
      decodeShort (axisWord n l c) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨j, rfl⟩ := (baseBIndexEquiv n).surjective i
    simp only [simpleReflectionWord_cons, Equiv.Perm.mul_apply, ih,
      simple_reflection_axis, axisWord, Equiv.symm_apply_apply]

theorem axisHeight_word_le (n : ℕ) (l : List (baseB n).support)
    (c : Fin (n + 1) × Bool) :
    axisHeight n (axisWord n l c) ≤ axisHeight n c + l.length := by
  induction l with
  | nil => simp [axisWord]
  | cons i l ih =>
    have h := axisHeight_step_le n ((baseBIndexEquiv n).symm i) (axisWord n l c)
    change axisHeight n (axisStep n ((baseBIndexEquiv n).symm i) (axisWord n l c)) ≤ _
    simp only [List.length_cons]
    omega

/-- The orbit distance lower-bounds every actual Weyl-word length. -/
theorem axisHeight_le_rootWeylLength (n : ℕ) (w : W n) (c : Fin (n + 1) × Bool)
    (hc : w.val (seed n) = decodeShort c) :
    axisHeight n c ≤ rootWeylLength (pairingB (n + 1)) (baseB n) w := by
  obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec (pairingB (n + 1)) (baseB n) w
  have he : decodeShort (axisWord n l (0, true)) = decodeShort c := by
    rw [← simpleReflectionWord_axis, hl]
    exact hc
  have hlabel := decodeShort_injective he
  have h := axisHeight_word_le n l (0, true)
  simpa only [hlabel, axisHeight, Bool.true_eq, ↓reduceIte, Fin.val_zero, zero_add, hlen] using h

end Atlas.Chevalley.ClassicalBParabolic
