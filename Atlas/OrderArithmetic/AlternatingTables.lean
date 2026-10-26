import Atlas.OrderArithmetic.FiniteTables
import Mathlib.Tactic.IntervalCases

namespace Atlas.OrderArithmetic

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_5 : orderCandidates (order (.alternating 5)) = {.linear 2 4, .linear 2 5} := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 3, 5])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_6 : orderCandidates (order (.alternating 6)) = {.linear 2 9} := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 3, 3, 5])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_7 : orderCandidates (order (.alternating 7)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 3, 3, 5, 7])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_8 : orderCandidates (order (.alternating 8)) = {.linear 4 2, .linear 3 4} := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 3, 3, 5, 7])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_9 : orderCandidates (order (.alternating 9)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 7])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_10 : orderCandidates (order (.alternating 10)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 5, 7])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_11 : orderCandidates (order (.alternating 11)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 5, 7, 11])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_12 : orderCandidates (order (.alternating 12)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 7, 11])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_13 : orderCandidates (order (.alternating 13)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 7, 11, 13])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_14 : orderCandidates (order (.alternating 14)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5, 7, 7, 11, 13])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_15 : orderCandidates (order (.alternating 15)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 7, 11, 13])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_16 : orderCandidates (order (.alternating 16)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 7, 11, 13])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_17 : orderCandidates (order (.alternating 17)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 7, 11, 13, 17])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_18 : orderCandidates (order (.alternating 18)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 7, 11, 13, 17])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

-- Certified finite evaluation after the unbounded factorial cutoff.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem alternating_candidates_19 : orderCandidates (order (.alternating 19)) = ∅ := by
  rw [orderCandidates_eq_from_factors (L := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 7, 7, 11, 13, 17, 19])
    (by norm_num [order, Nat.factorial]) (by decide +kernel)]
  decide +kernel

/-- Every alternating/Lie numerical equality is in the explicit collision relation. -/
theorem alternating_lie_collision {x : RawEntry} {n : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hn : 5 ≤ n)
    (heq : order x = order (.alternating n)) : Collision x (.alternating n) := by
  have hb := alternating_lie_degree_bound hx hl hn heq
  have hc := mem_orderCandidates_of_order_eq hx hl heq
  interval_cases n
  · rw [alternating_candidates_5] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    all_goals norm_num [Collision, normalize, Exceptional]
  · rw [alternating_candidates_6] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    subst x
    all_goals norm_num [Collision, normalize, Exceptional]
  · rw [alternating_candidates_7] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_8] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    all_goals norm_num [Collision, normalize, Exceptional]
  · rw [alternating_candidates_9] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_10] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_11] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_12] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_13] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_14] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_15] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_16] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_17] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_18] at hc
    exact False.elim (Finset.notMem_empty x hc)
  · rw [alternating_candidates_19] at hc
    exact False.elim (Finset.notMem_empty x hc)

theorem alternating_lie_order_iff {x : RawEntry} {n : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hn : 5 ≤ n) :
    order x = order (.alternating n) ↔ Collision x (.alternating n) :=
  ⟨alternating_lie_collision hx hl hn, collision_order⟩

end Atlas.OrderArithmetic
