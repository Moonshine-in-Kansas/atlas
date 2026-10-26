import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic

/-! A finite integer-graded coordinate filtration. -/
namespace Atlas.LinearAlgebra

variable {R M I : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The map e-1 strictly lowers a bounded coordinate filtration. Redundant
coordinates are allowed: only injectivity of the total readout is required. -/
theorem coordinate_lowering_pow_eq_zero
    (read : M →ₗ[R] (I → R)) (hread : Function.Injective read)
    (grade : I → ℤ) (lo hi : ℤ)
    (hlo : ∀ i, lo ≤ grade i) (hhi : ∀ i, grade i ≤ hi)
    (e : Module.End R M)
    (he : ∀ v i, (∀ j, grade i < grade j → read v j = 0) → read (e v) i = read v i)
    (d : ℕ) (hd : hi - (d : ℤ) < lo) :
    (e - 1) ^ d = 0 := by
  have filtration : ∀ n : ℕ, ∀ v i,
      hi - (n : ℤ) < grade i → read (((e - 1) ^ n) v) i = 0 := by
    intro n
    induction n with
    | zero =>
        intro v i h
        have := hhi i
        simp only [Nat.cast_zero, sub_zero] at h
        omega
    | succ n ih =>
        intro v i h
        rw [pow_succ', Module.End.mul_apply]
        simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, Pi.sub_apply]
        apply sub_eq_zero.mpr
        apply he
        intro j hj
        apply ih v j
        push_cast at h
        omega
  apply LinearMap.ext
  intro v
  apply hread
  ext i
  simp only [LinearMap.zero_apply, map_zero, Pi.zero_apply]
  apply filtration d v i
  exact lt_of_lt_of_le hd (hlo i)

/-- Pure ring consequence used after the filtration result. -/
theorem pow_thirtyTwo_eq_one_of_sub_one_pow_twentyFive_eq_zero
    {A : Type*} [Ring A] [CharP A 2] (e : A)
    (h : (e - 1) ^ 25 = 0) : e ^ 32 = 1 := by
  have hz : (e - 1) ^ 32 = 0 := pow_eq_zero_of_le (by decide : 25 ≤ 32) h
  have hp := add_pow_char_pow_of_commute (p := 2) (n := 5)
    (Commute.one_right (e - 1))
  norm_num only [show (2 : ℕ)^5 = 32 by decide, one_pow] at hp
  rw [sub_add_cancel, hz, zero_add] at hp
  exact hp

/-- No order target is involved: bounded element exponent already makes a group
 a 2-group. Finiteness is needed only for nilpotence and solvability. -/
theorem isPGroup_two_of_pow_thirtyTwo {G : Type*} [Group G]
    (h : ∀ g : G, g ^ 32 = 1) : IsPGroup 2 G := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  exact ⟨5, by simpa using h g⟩

theorem solvable_of_pow_thirtyTwo {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, g ^ 32 = 1) : Group.IsSolvable G := by
  letI : Group.IsNilpotent G := (isPGroup_two_of_pow_thirtyTwo h).isNilpotent
  infer_instance

end Atlas.LinearAlgebra
