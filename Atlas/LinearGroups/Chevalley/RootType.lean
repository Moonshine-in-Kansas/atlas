/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the repository license; see LICENSE.
-/
import Mathlib.Data.List.Range
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.GCD.Basic
import Lean.Elab.Tactic.Omega

/-! # Validated untwisted root-type parameters

This file specifies parameters and arithmetic targets. It does not construct a root system
or a group, nor assert that any group has the displayed order. The list of degrees retains
multiplicity, particularly the repeated degree in even type D.
-/

namespace Atlas.Chevalley

/-- The core root-type domain. Classical ranks are unbounded natural parameters. -/
inductive RootType where
  | A (r : ℕ) (valid : 1 ≤ r)
  | B (r : ℕ) (valid : 2 ≤ r)
  | C (r : ℕ) (valid : 2 ≤ r)
  | D (r : ℕ) (valid : 4 ≤ r)
  | E6 | E7 | E8 | F4 | G2
  deriving DecidableEq

namespace RootType

/-- Lie rank, distinct from matrix dimension and field cardinality. -/
def rank : RootType → ℕ
  | A r _ | B r _ | C r _ | D r _ => r
  | E6 => 6 | E7 => 7 | E8 => 8 | F4 => 4 | G2 => 2

/-- Target positive-root number. Identification with actual positive roots is a later theorem. -/
def positiveRootNumber : RootType → ℕ
  | A r _ => r * (r + 1) / 2
  | B r _ | C r _ => r ^ 2
  | D r _ => r * (r - 1)
  | E6 => 36 | E7 => 63 | E8 => 120 | F4 => 24 | G2 => 6

/-- Fundamental-degree specification, as a list rather than a set. -/
def degrees : RootType → List ℕ
  | A r _ => (List.range r).map (fun i => i + 2)
  | B r _ | C r _ => (List.range r).map (fun i => 2 * (i + 1))
  | D r _ => (List.range (r - 1)).map (fun i => 2 * (i + 1)) ++ [r]
  | E6 => [2, 5, 6, 8, 9, 12]
  | E7 => [2, 6, 8, 10, 12, 14, 18]
  | E8 => [2, 8, 12, 14, 18, 20, 24, 30]
  | F4 => [2, 6, 8, 12]
  | G2 => [2, 6]

/-- Target finite-point center factor; not the integral Cartan determinant. -/
def centerFactor : RootType → ℕ → ℕ
  | A r _, q => Nat.gcd (r + 1) (q - 1)
  | B _ _, q | C _ _, q | E7, q => Nat.gcd 2 (q - 1)
  | D r _, q => Nat.gcd 4 (q ^ r - 1)
  | E6, q => Nat.gcd 3 (q - 1)
  | E8, _ | F4, _ | G2, _ => 1

/-- The target simply connected order polynomial, without a group-cardinality assertion. -/
def orderPolynomial (Φ : RootType) (q : ℕ) : ℕ :=
  q ^ Φ.positiveRootNumber * ((Φ.degrees.map (fun d => q ^ d - 1)).prod)

/-- Parameter contract for nonabelian simplicity. This is not yet a simplicity theorem. -/
def Good (Φ : RootType) (q : ℕ) : Prop :=
  2 ≤ q ∧ match Φ with
    | A r _ => r ≠ 1 ∨ (q ≠ 2 ∧ q ≠ 3)
    | B r _ | C r _ => r ≠ 2 ∨ q ≠ 2
    | G2 => q ≠ 2
    | _ => True

instance (Φ : RootType) (q : ℕ) : Decidable (Φ.Good q) := by
  unfold Good
  cases Φ <;> infer_instance

theorem rank_pos (Φ : RootType) : 0 < Φ.rank := by
  cases Φ <;> simp only [rank] <;> omega

@[simp] theorem degrees_length (Φ : RootType) : Φ.degrees.length = Φ.rank := by
  cases Φ <;> simp [degrees, rank]
  omega

/-- Every entry in the specified degree list is at least two. -/
theorem two_le_degree (Φ : RootType) {d : ℕ} (hd : d ∈ Φ.degrees) : 2 ≤ d := by
  cases Φ <;> simp only [degrees, List.mem_map, List.mem_range,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  all_goals obtain ⟨i, _, rfl⟩ := hd
  all_goals omega

/-- The repeated middle degree is retained uniformly at every even classical D rank. -/
theorem d_even_repeated_degree (k : ℕ) (hk : 2 ≤ k) :
    ((D (2 * k) (by omega)).degrees).count (2 * k) = 2 := by
  have hmul : Function.Injective (fun i : ℕ => 2 * (i + 1)) := by
    intro i j hij
    dsimp at hij
    omega
  have hk₁ : 2 * (k - 1 + 1) = 2 * k := by omega
  have hm : k - 1 ∈ List.range (2 * k - 1) := by
    simp only [List.mem_range]
    omega
  have hc : (List.range (2 * k - 1)).count (k - 1) = 1 :=
    List.count_eq_one_of_mem List.nodup_range hm
  have hmap := List.count_map_of_injective (List.range (2 * k - 1))
    (fun i : ℕ => 2 * (i + 1)) hmul (k - 1)
  simp only [hk₁] at hmap
  simp only [degrees, List.count_append, hmap, hc]
  simp

/-- Even D retains both occurrences of the middle degree; the smallest regression case. -/
theorem d4_repeated_degree : ((D 4 (by decide)).degrees).count 4 = 2 := by decide

theorem d4_degrees : (D 4 (by decide)).degrees = [2, 4, 6, 4] := rfl

theorem e6_center_at_four : E6.centerFactor 4 = 3 := by decide

theorem e7_center_at_three : E7.centerFactor 3 = 2 := by decide

theorem f4_binary_good : F4.Good 2 := by decide

theorem d4_binary_good : (D 4 (by decide)).Good 2 := by decide

theorem e6_binary_good : E6.Good 2 := by decide

theorem e7_binary_good : E7.Good 2 := by decide

theorem e8_binary_good : E8.Good 2 := by decide

theorem a1_binary_not_good : ¬ (A 1 (by decide)).Good 2 := by decide

theorem a1_ternary_not_good : ¬ (A 1 (by decide)).Good 3 := by decide

theorem b2_binary_not_good : ¬ (B 2 (by decide)).Good 2 := by decide

theorem c2_binary_not_good : ¬ (C 2 (by decide)).Good 2 := by decide

theorem g2_binary_not_good : ¬ G2.Good 2 := by decide

end RootType
end Atlas.Chevalley
