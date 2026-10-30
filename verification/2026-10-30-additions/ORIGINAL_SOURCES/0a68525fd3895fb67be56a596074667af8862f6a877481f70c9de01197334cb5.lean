import ComparisonWork.J1WhitelawFirstOrbit

/-!
Uncompiled source-only finite rows. All vectors and coordinate operations are
those of the verified Whitelaw modules. Each nontrivial pair row is split by
its second seed before ordinary kernel decision; no external table is supplied.
-/
namespace Atlas.Janko1

/-- The squared-coordinate consequence of actual signed projective transport. -/
abbrev WhitelawSquareMatch (r s : Fin 10) (i : Fin 7) (j : Fin 3) (c : Field) : Prop :=
  ∀ k : Fin 7,
    ((coordinateShift^[i.val] (coordinateDouble^[j.val] (whitelawSeed r))) k) ^ 2 =
      c ^ 2 * (whitelawSeed s k) ^ 2

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_1 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 1 1 i j c → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_2 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 2 2 i j c → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_3 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 3 3 i j c → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_4 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 4 4 i j c → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_5 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 5 5 i j c → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_6 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 6 6 i j c → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_7 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 7 7 i j c → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_8 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 8 8 i j c → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_self_9 : ∀ (i : Fin 7) (j : Fin 3) (c : Field),
    WhitelawSquareMatch 9 9 i j c → i = 0 ∧ j = 0 := by
  decide

/-- The first row is reused from the verified first-orbit module. -/
theorem whitelawSquareMatch_self_rigid (r : Fin 10) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      WhitelawSquareMatch r r i j c → i = 0 ∧ j = 0 := by
  fin_cases r
  · exact firstSeed_permutation_square_rigid
  · exact whitelaw_square_self_1
  · exact whitelaw_square_self_2
  · exact whitelaw_square_self_3
  · exact whitelaw_square_self_4
  · exact whitelaw_square_self_5
  · exact whitelaw_square_self_6
  · exact whitelaw_square_self_7
  · exact whitelaw_square_self_8
  · exact whitelaw_square_self_9

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_0 (s : Fin 10) (hrs : (0 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 0 s i j c := by
  change (0 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_1 (s : Fin 10) (hrs : (1 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 1 s i j c := by
  change (1 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_2 (s : Fin 10) (hrs : (2 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 2 s i j c := by
  change (2 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_3 (s : Fin 10) (hrs : (3 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 3 s i j c := by
  change (3 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_4 (s : Fin 10) (hrs : (4 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 4 s i j c := by
  change (4 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_5 (s : Fin 10) (hrs : (5 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 5 s i j c := by
  change (5 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_6 (s : Fin 10) (hrs : (6 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 6 s i j c := by
  change (6 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_7 (s : Fin 10) (hrs : (7 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 7 s i j c := by
  change (7 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

set_option maxRecDepth 8192 in
theorem whitelaw_square_separate_row_8 (s : Fin 10) (hrs : (8 : Fin 10) < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      ¬ WhitelawSquareMatch 8 s i j c := by
  change (8 : Nat) < s.val at hrs
  fin_cases s <;> norm_num at hrs
  all_goals decide

/-- Only the 45 ordered distinct seed pairs are decided. Reverse transport will
be handled by symmetry of the actual H-orbit relation. -/
theorem whitelawSquareMatch_lt_false (r s : Fin 10) (hrs : r < s) :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field), ¬ WhitelawSquareMatch r s i j c := by
  fin_cases r
  · exact whitelaw_square_separate_row_0 s hrs
  · exact whitelaw_square_separate_row_1 s hrs
  · exact whitelaw_square_separate_row_2 s hrs
  · exact whitelaw_square_separate_row_3 s hrs
  · exact whitelaw_square_separate_row_4 s hrs
  · exact whitelaw_square_separate_row_5 s hrs
  · exact whitelaw_square_separate_row_6 s hrs
  · exact whitelaw_square_separate_row_7 s hrs
  · exact whitelaw_square_separate_row_8 s hrs
  · have hv : (9 : Nat) < s.val := hrs
    omega

end Atlas.Janko1
