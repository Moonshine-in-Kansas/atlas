import Atlas.LinearGroups.Chevalley.RootData.ClassicalDParabolicFunctional
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDAction

/-! The signed coordinate functions on actual D roots. Every actual Weyl
word permutes these functions, and the first coordinate reaches every sign
and coordinate. This does not identify the whole Weyl group with a signed
permutation group. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDParabolic
open Classical ClassicalData RootData Integral.Minuscule.TypeD

def rootCoordinate (n : ℕ) (c : Fin (n + 3) × Bool) : DRoot (n + 3) → ℤ :=
  fun β => sign c.2 * β.val c.1

private def rootReflection (n : ℕ) (α : DRoot (n + 3)) :
    (pairingD (n + 3)).weylGroupToPerm.range :=
  ⟨(pairingD (n + 3)).reflectionPerm α, by
    rw [(pairingD (n + 3)).range_weylGroupToPerm]
    exact Subgroup.subset_closure ⟨α, rfl⟩⟩

theorem rootCoordinate_reflection (n : ℕ) (α : DRoot (n + 3))
    (c : Fin (n + 3) × Bool) :
    ∃ d : Fin (n + 3) × Bool, ∀ β : DRoot (n + 3),
      rootCoordinate n c ((pairingD (n + 3)).reflectionPerm α β) =
        rootCoordinate n d β := by
  rcases signed_support_classification α with ⟨h, _⟩ | ⟨i, j, hij, t, u, ht, hu, hα⟩
  · cases h
  · have he : α = longRoot false i j hij t u ht hu := Subtype.ext hα
    subst α
    obtain ⟨b, hb⟩ : ∃ b : Bool, sign b = sign c.2 * (-t * u) := by
      refine ⟨decide (sign c.2 * (-t * u) = 1), ?_⟩
      rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;> cases c.2 <;>
        norm_num [sign]
    by_cases hi : c.1 = i
    · refine ⟨(j, b), ?_⟩
      intro β
      change sign c.2 * reflect (longRoot false i j hij t u ht hu) β.val c.1 =
        sign b * β.val j
      rw [reflect_long_coordinates]
      simp only [hi, ite_true, hb]
      ring
    · by_cases hj : c.1 = j
      · refine ⟨(i, b), ?_⟩
        intro β
        change sign c.2 * reflect (longRoot false i j hij t u ht hu) β.val c.1 =
          sign b * β.val i
        rw [reflect_long_coordinates]
        simp only [hj, Ne.symm hij, ite_false, ite_true, hb]
        ring
      · refine ⟨c, ?_⟩
        intro β
        change sign c.2 * reflect (longRoot false i j hij t u ht hu) β.val c.1 =
          sign c.2 * β.val c.1
        rw [reflect_long_coordinates]
        simp only [hi, hj, ite_false]

theorem rootCoordinate_weyl (n : ℕ)
    (w : (pairingD (n + 3)).weylGroupToPerm.range) (c : Fin (n + 3) × Bool) :
    ∃ d : Fin (n + 3) × Bool, ∀ β : DRoot (n + 3),
      rootCoordinate n c (w.val β) = rootCoordinate n d β := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem
    (pairingD (n + 3)) (baseD (n + 1)) w.property
  have hword : ∀ l : List (baseD (n + 1)).support, ∀ c : Fin (n + 3) × Bool,
      ∃ d : Fin (n + 3) × Bool, ∀ β : DRoot (n + 3),
        rootCoordinate n c (simpleReflectionWord (pairingD (n + 3)) (baseD (n + 1)) l β) =
          rootCoordinate n d β := by
    intro l
    induction l with
    | nil => intro c; exact ⟨c, fun _ => rfl⟩
    | cons i l ih =>
      intro c
      obtain ⟨e, he⟩ := rootCoordinate_reflection n i.val c
      obtain ⟨d, hd⟩ := ih e
      refine ⟨d, ?_⟩
      intro β
      change rootCoordinate n c ((pairingD (n + 3)).reflectionPerm i.val
        (simpleReflectionWord (pairingD (n + 3)) (baseD (n + 1)) l β)) = _
      rw [he, hd]
  simpa only [hl] using hword l c

/-- Every signed coordinate is the actual first row of an actual Weyl element. -/
theorem rootCoordinate_reachable (n : ℕ) (c : Fin (n + 3) × Bool) :
    ∃ w : (pairingD (n + 3)).weylGroupToPerm.range,
      ∀ β : DRoot (n + 3), (w.val β).val 0 = rootCoordinate n c β := by
  rcases c with ⟨k, b⟩
  by_cases hk : k = 0
  · subst k
    cases b with
    | true => exact ⟨1, fun β => by simp [rootCoordinate, sign]⟩
    | false =>
      let p : Fin (n + 3) := ⟨1, by omega⟩
      have hp : (0 : Fin (n + 3)) ≠ p := by
        intro he
        have hh := congrArg Fin.val he
        change (0 : ℕ) = 1 at hh
        omega
      let a := longRoot false 0 p hp 1 1 (Or.inl rfl) (Or.inl rfl)
      let d := longRoot false 0 p hp 1 (-1) (Or.inl rfl) (Or.inr rfl)
      refine ⟨rootReflection n a * rootReflection n d, ?_⟩
      intro β
      change reflect a (reflect d β.val) 0 = rootCoordinate n (0, false) β
      dsimp only [a, d]
      rw [reflect_long_coordinates]
      simp only [ite_true, neg_mul, one_mul]
      rw [reflect_long_coordinates]
      simp [rootCoordinate, sign, Ne.symm hp]
  · cases b with
    | true =>
      refine ⟨rootReflection n (longRoot false 0 k (Ne.symm hk) 1 (-1)
        (Or.inl rfl) (Or.inr rfl)), ?_⟩
      intro β
      change reflect (longRoot false 0 k (Ne.symm hk) 1 (-1)
        (Or.inl rfl) (Or.inr rfl)) β.val 0 = rootCoordinate n (k, true) β
      rw [reflect_long_coordinates]
      simp [rootCoordinate, sign]
    | false =>
      refine ⟨rootReflection n (longRoot false 0 k (Ne.symm hk) 1 1
        (Or.inl rfl) (Or.inl rfl)), ?_⟩
      intro β
      change reflect (longRoot false 0 k (Ne.symm hk) 1 1
        (Or.inl rfl) (Or.inl rfl)) β.val 0 = rootCoordinate n (k, false) β
      rw [reflect_long_coordinates]
      simp [rootCoordinate, sign]

/-- Actual D roots distinguish all 2r signed coordinate functions. -/
theorem rootCoordinate_injective (n : ℕ) : Function.Injective (rootCoordinate n) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hki⟩ := exists_ne i
    have he := congrFun h (longRoot false i k (Ne.symm hki) 1 1 (Or.inl rfl) (Or.inl rfl))
    cases b <;> cases c <;>
      simp_all [rootCoordinate, sign, longRoot, Ne.symm hki]
  · have hp := congrFun h (longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl))
    have hm := congrFun h (longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl))
    cases b <;> cases c <;>
      simp_all [rootCoordinate, sign, longRoot, Ne.symm hij]

end Atlas.Chevalley.ClassicalDParabolic
