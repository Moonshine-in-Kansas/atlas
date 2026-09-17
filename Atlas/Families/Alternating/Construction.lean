import Atlas.Families.Alternating.Action

namespace Atlas.Families.Alternating

structure Construction (n : ℕ) : Prop where
  finite : Finite (Model n)
  card : Nat.card (Model n) = order n
  simple : IsSimpleGroup (Model n)
  noncommuting : ∃ a b : Model n, a * b ≠ b * a
  normal : (alternatingGroup (Fin n)).Normal
  index : (alternatingGroup (Fin n)).index = 2
  faithful : FaithfulSMul (Model n) (Fin n)
  generation : Subgroup.closure {g : Equiv.Perm (Fin n) | g.IsThreeCycle} = alternatingGroup (Fin n)
  transitivity : ∀ k, k ≤ n - 2 → MulAction.IsMultiplyPretransitive (Model n) (Fin n) k
  not_transitivity : ¬ MulAction.IsMultiplyPretransitive (Model n) (Fin n) (n - 1)
  stabilizer : ∀ k (e : Fin k ↪ Fin n), Nonempty (PointwiseStabilizer e ≃* Model (n - k))
  stabilizer_card : ∀ k (e : Fin k ↪ Fin n), Nat.card (PointwiseStabilizer e) = order (n - k)

theorem construction (n : ℕ) (hn : IsAdmissible n) : Construction n where
  finite := finite n
  card := card n
  simple := isSimpleGroup n hn
  noncommuting := exists_mul_ne_mul n (le_trans (by decide) hn)
  normal := normal n
  index := index n (le_trans (by decide) hn)
  faithful := faithful n
  generation := generation n
  transitivity := multiply_transitive n
  not_transitivity := not_multiply_transitive n hn
  stabilizer := fun _ e => ⟨stabilizerEquiv e⟩
  stabilizer_card := fun _ e => stabilizer_card e

theorem exists_model (n : ℕ) (hn : IsAdmissible n) :
    ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model n) ∧ Finite G ∧
      Nat.card G = order n ∧ IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧
      Construction n := by
  exact ⟨Model n, inferInstance, ⟨MulEquiv.refl _⟩, finite n, card n,
    isSimpleGroup n hn, exists_mul_ne_mul n (le_trans (by decide) hn), construction n hn⟩

theorem checks_five : Nat.card (Model 5) = 60 ∧ Construction 5 := by
  exact ⟨by rw [card_factorial 5 (by decide)]; decide, construction 5 (by exact le_rfl)⟩
theorem checks_six : Nat.card (Model 6) = 360 ∧ Construction 6 := by
  exact ⟨by rw [card_factorial 6 (by decide)]; decide, construction 6 (by change 5 ≤ 6; decide)⟩
theorem checks_seven : Nat.card (Model 7) = 2520 ∧ Construction 7 := by
  exact ⟨by rw [card_factorial 7 (by decide)]; decide, construction 7 (by change 5 ≤ 7; decide)⟩
theorem checks_eight : Nat.card (Model 8) = 20160 ∧ Construction 8 := by
  exact ⟨by rw [card_factorial 8 (by decide)]; decide, construction 8 (by change 5 ≤ 8; decide)⟩
theorem checks_small : (Nat.card (Model 0) = 1 ∧ ¬ IsSimpleGroup (Model 0)) ∧
    (Nat.card (Model 1) = 1 ∧ ¬ IsSimpleGroup (Model 1)) ∧
    (Nat.card (Model 2) = 1 ∧ ¬ IsSimpleGroup (Model 2)) ∧
    (Nat.card (Model 3) = 3 ∧ IsSimpleGroup (Model 3)) ∧
    (Nat.card (Model 4) = 12 ∧ ¬ IsSimpleGroup (Model 4)) := by
  refine ⟨⟨?_, not_simple_small 0 (by decide)⟩,
    ⟨?_, not_simple_small 1 (by decide)⟩,
    ⟨?_, not_simple_small 2 (by decide)⟩,
    ⟨?_, simple_three⟩, ⟨?_, not_simple_four⟩⟩
  all_goals rw [card]; norm_num [order, Nat.factorial]

end Atlas.Families.Alternating
