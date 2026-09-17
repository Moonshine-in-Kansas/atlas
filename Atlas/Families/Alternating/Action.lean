import Atlas.Families.Alternating.Stabilizers

namespace Atlas.Families.Alternating

theorem multiply_transitive (n k : ℕ) (hk : k ≤ n - 2) :
    MulAction.IsMultiplyPretransitive (Model n) (Fin n) k := by
  have ht : MulAction.IsMultiplyPretransitive (Model n) (Fin n) (n - 2) := by
    simpa only [Nat.card_fin] using alternatingGroup.isMultiplyPretransitive (Fin n)
  exact MulAction.isMultiplyPretransitive_of_le hk (by simp)

theorem not_multiply_transitive (n : ℕ) (hn : 5 ≤ n) :
    ¬ MulAction.IsMultiplyPretransitive (Model n) (Fin n) (n - 1) := by
  intro ht
  let e : Fin (n - 1) ↪ Fin n := Fin.castLEEmb (by omega)
  have hs : (tuplePoints e : Set (Fin n)).ncard = n - 1 := by
    simp only [Set.ncard_coe_finset, tuplePoints, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have hi := ht.index_of_fixingSubgroup_mul hs
  have hsub : n - (n - 1) = 1 := by omega
  simp only [Nat.card_fin, hsub, Nat.factorial_one, mul_one] at hi
  have hprod := (PointwiseStabilizer e).card_mul_index
  change Nat.card (PointwiseStabilizer e) *
    (fixingSubgroup (Model n) (tuplePoints e : Set (Fin n))).index = Nat.card (Model n) at hprod
  rw [hi] at hprod
  have hp : 0 < Nat.card (PointwiseStabilizer e) := Nat.card_pos
  have hf := Nat.factorial_pos n
  have hc := card_mul_two n (by omega)
  nlinarith

end Atlas.Families.Alternating
