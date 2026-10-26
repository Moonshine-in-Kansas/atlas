import Atlas.OrderArithmetic.FixedCandidates
import Atlas.OrderArithmetic.ElementaryReduction
import Atlas.OrderArithmetic.Regression

namespace Atlas.OrderArithmetic

/-- Computable necessary rank conditions; this does not assert prime-power admissibility. -/
def rankAllowed : RawEntry → Bool
  | .linear d _ => 2 ≤ d
  | .unitary d _ => 3 ≤ d
  | .B r _ | .C r _ => 2 ≤ r
  | .Dplus r _ | .Dminus r _ => 4 ≤ r
  | _ => true

theorem rankAllowed_of_admissible {x : RawEntry} (hx : Admissible x) :
    rankAllowed x = true := by
  cases x <;> simp only [rankAllowed, decide_eq_true_eq]
  all_goals exact hx.1

/-- Filter each rank before taking unions, so irrelevant ranks do not enlarge the sets. -/
def exactAt (q a : ℕ) : Finset RawEntry :=
  ((Finset.Icc 2 (a + 1)).biUnion fun r => (classicalAt r q).filter
    fun x => rankAllowed x = true ∧ characteristicExponent x = a) ∪
    ((exceptionalAt q).filter fun x => rankAllowed x = true ∧ characteristicExponent x = a)

theorem exactAt_eq (q a : ℕ) : exactAt q a = (ordinaryAt q a).filter
    (fun x => rankAllowed x = true ∧ characteristicExponent x = a) := by
  simp only [exactAt, ordinaryAt, Finset.filter_union, Finset.filter_biUnion]

/-- A valuation-exact candidate set, with equality of numerical orders checked last. -/
def orderCandidates (M : ℕ) : Finset RawEntry :=
  M.primeFactors.biUnion fun p =>
    ((Finset.Icc 1 (M.factorization p)).filter fun f => f ∣ M.factorization p).biUnion
      fun f => (exactAt (p ^ f) (M.factorization p / f)).filter
          fun x => order x = M

theorem mem_orderCandidates_of_order_eq {x : RawEntry} {M : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hM : order x = M) : x ∈ orderCandidates M := by
  simp only [orderCandidates, exactAt_eq]
  obtain ⟨p, f, hp, hf, hq⟩ := lie_field_primePower hx hl
  have ha := characteristicExponent_pos hx hl
  have hv : M.factorization p = f * characteristicExponent x := by
    rw [← hM]
    exact order_characteristic_valuation hx hl hp hf hq
  have hpos : M ≠ 0 := by have := lie_order_pos hx hl; omega
  have hpM : p ∣ M := (hp.dvd_iff_one_le_factorization hpos).mpr (by rw [hv]; nlinarith)
  apply Finset.mem_biUnion.mpr
  refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpM, hpos⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hf, ?_⟩, ?_⟩, ?_⟩
  · rw [hv]; nlinarith
  · exact ⟨characteristicExponent x, hv⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hM⟩
    · rw [hv, Nat.mul_div_cancel_left _ (by omega : 0 < f), ← hq]
      exact self_mem_ordinaryAt hx hl
    · exact ⟨rankAllowed_of_admissible hx, by rw [hv, Nat.mul_div_cancel_left _ (by omega : 0 < f)]⟩

set_option maxRecDepth 4096 in
-- Kernel reduction checks the complete finite candidate set.\nset_option maxHeartbeats 800000 in
theorem candidates_504 : orderCandidates 504 = {.linear 2 8} := by
  simp only [orderCandidates, ← Nat.primeFactorsList_count_eq]
  decide +kernel

set_option maxRecDepth 4096 in
-- Kernel reduction checks the complete finite candidate set.\nset_option maxHeartbeats 800000 in
theorem candidates_6048 : orderCandidates 6048 = {.unitary 3 3} := by
  simp only [orderCandidates, ← Nat.primeFactorsList_count_eq]
  decide +kernel

set_option maxRecDepth 4096 in
-- Kernel reduction checks the complete finite candidate set.\nset_option maxHeartbeats 800000 in
theorem candidates_25920 : orderCandidates 25920 = {.unitary 4 2, .B 2 3, .C 2 3} := by
  simp only [orderCandidates, ← Nat.primeFactorsList_count_eq]
  decide +kernel

theorem order_eq_504_iff {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    order x = 504 ↔ x = .linear 2 8 := by
  constructor
  · intro h
    simpa [candidates_504] using mem_orderCandidates_of_order_eq hx hl h
  · rintro rfl
    exact regression_504

theorem order_eq_6048_iff {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    order x = 6048 ↔ x = .unitary 3 3 := by
  constructor
  · intro h
    simpa [candidates_6048] using mem_orderCandidates_of_order_eq hx hl h
  · rintro rfl
    exact regression_6048

theorem order_eq_25920_iff {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    order x = 25920 ↔ x = .unitary 4 2 ∨ x = .B 2 3 ∨ x = .C 2 3 := by
  constructor
  · intro h
    simpa [candidates_25920] using mem_orderCandidates_of_order_eq hx hl h
  · rintro (rfl | rfl | rfl)
    · exact order_unitary_4_2
    · exact order_C_2_3
    · exact order_C_2_3

/-- Evaluate using a supplied factor list, whose product and primality are proved separately. -/
def candidatesFromFactors (M : ℕ) (L : List ℕ) : Finset RawEntry :=
  L.toFinset.biUnion fun p =>
    ((Finset.Icc 1 (L.count p)).filter fun f => f ∣ L.count p).biUnion
      fun f => (exactAt (p ^ f) (L.count p / f)).filter
          fun x => order x = M

theorem orderCandidates_eq_from_factors {M : ℕ} {L : List ℕ}
    (hprod : L.prod = M) (hprime : ∀ p ∈ L, p.Prime) :
    orderCandidates M = candidatesFromFactors M L := by
  have hperm := Nat.primeFactorsList_unique hprod hprime
  have hs : L.toFinset = M.primeFactorsList.toFinset := by
    ext p
    simpa using hperm.mem_iff
  simp only [orderCandidates, candidatesFromFactors, ← Nat.primeFactorsList_count_eq,
    Nat.primeFactors, hs, hperm.count_eq]

end Atlas.OrderArithmetic

