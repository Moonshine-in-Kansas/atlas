import Atlas.OrderArithmetic.FixedCandidates
import Atlas.OrderArithmetic.ExponentReduction
import Mathlib.Tactic.Linarith

namespace Atlas.OrderArithmetic

/-! Numerical profiles and rank bounds for the arithmetic comparison programme.

`topIndex` records the proposed largest-index table. This module proves arithmetic
facts about that table only: it does not identify cyclotomic support, prove a
primitive-divisor theorem, or deduce index equality from equality of orders.
-/

/-- The numerical top-index profile, before any assertion about cyclotomic support. -/
def topIndex : RawEntry → ℕ
  | .linear d _ => d
  | .unitary d _ => if Even d then 2 * (d - 1) else 2 * d
  | .B r _ | .C r _ | .Dminus r _ => 2 * r
  | .Dplus r _ => 2 * (r - 1)
  | .G2 _ | .smallRee _ => 6
  | .F4 _ | .E6 _ | .trialityD4 _ | .largeRee _ => 12
  | .E7 _ | .twistedE6 _ => 18
  | .E8 _ => 30
  | .suzuki _ => 4
  | _ => 0

def IsExceptionalLie : RawEntry → Prop
  | .G2 _ | .F4 _ | .E6 _ | .E7 _ | .E8 _ | .twistedE6 _
      | .trialityD4 _ | .suzuki _ | .smallRee _ | .largeRee _ => True
  | _ => False

theorem topIndex_two_le {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    2 ≤ topIndex x := by
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear d q => exact hx.1
  | unitary d q =>
    have hd : 3 ≤ d := hx.1
    simp only [topIndex]
    split <;> omega
  | B r q | C r q | Dplus r q | Dminus r q =>
    have hr := hx.1
    simp only [topIndex]
    omega
  | _ => norm_num [topIndex]

theorem exceptional_exponent_le_four_topIndex {x : RawEntry}
    (hx : IsExceptionalLie x) : characteristicExponent x ≤ 4 * topIndex x := by
  cases x <;> simp_all [IsExceptionalLie, characteristicExponent, topIndex]

theorem linear_dimension_le_nine_of_index_ratio {d q : ℕ}
    (hd : 2 ≤ d)
    (h : characteristicExponent (.linear d q) ≤ 4 * topIndex (.linear d q)) :
    d ≤ 9 := by
  change d * (d - 1) / 2 ≤ 4 * d at h
  have ht : d * (d - 1) ≤ 8 * d + 1 := by omega
  have hs : d - 1 + 1 = d := by omega
  by_contra hn
  have hb : 10 ≤ d := by omega
  have hm := Nat.mul_le_mul_left d (show 9 ≤ d - 1 by omega)
  nlinarith

theorem unitary_dimension_le_seventeen_of_index_ratio {d q : ℕ}
    (hd : 3 ≤ d)
    (h : characteristicExponent (.unitary d q) ≤ 4 * topIndex (.unitary d q)) :
    d ≤ 17 := by
  have hm : topIndex (.unitary d q) ≤ 2 * d := by
    simp only [topIndex]
    split <;> omega
  have hh : d * (d - 1) / 2 ≤ 8 * d := by
    change d * (d - 1) / 2 ≤ 4 * topIndex (.unitary d q) at h
    omega
  have ht : d * (d - 1) ≤ 16 * d + 1 := by omega
  have hs : d - 1 + 1 = d := by omega
  by_contra hn
  have hb : 18 ≤ d := by omega
  have hm := Nat.mul_le_mul_left d (show 17 ≤ d - 1 by omega)
  nlinarith

theorem unitary_even_dimension_le_sixteen_of_index_ratio {d q : ℕ}
    (hd : 3 ≤ d) (he : Even d)
    (h : characteristicExponent (.unitary d q) ≤ 4 * topIndex (.unitary d q)) :
    d ≤ 16 := by
  simp only [characteristicExponent, topIndex, if_pos he] at h
  have ht : d * (d - 1) ≤ 16 * (d - 1) + 1 := by omega
  have hs : d - 1 + 1 = d := by omega
  by_contra hn
  have hb : 17 ≤ d := by omega
  have hm := Nat.mul_le_mul_right (d - 1) hb
  nlinarith

theorem BC_rank_le_eight_of_index_ratio {r : ℕ} (hr : 2 ≤ r)
    (h : r ^ 2 ≤ 4 * (2 * r)) : r ≤ 8 := by
  by_contra hn
  have hb : 9 ≤ r := by omega
  have hm := Nat.mul_le_mul_left r hb
  nlinarith

theorem Dplus_rank_le_eight_of_index_ratio {r q : ℕ} (hr : 4 ≤ r)
    (h : characteristicExponent (.Dplus r q) ≤ 4 * topIndex (.Dplus r q)) :
    r ≤ 8 := by
  change r * (r - 1) ≤ 4 * (2 * (r - 1)) at h
  have hs : r - 1 + 1 = r := by omega
  by_contra hn
  have hb : 9 ≤ r := by omega
  have hm := Nat.mul_le_mul_right (r - 1) hb
  nlinarith

theorem Dminus_rank_le_nine_of_index_ratio {r q : ℕ} (hr : 4 ≤ r)
    (h : characteristicExponent (.Dminus r q) ≤ 4 * topIndex (.Dminus r q)) :
    r ≤ 9 := by
  change r * (r - 1) ≤ 4 * (2 * r) at h
  have hs : r - 1 + 1 = r := by omega
  by_contra hn
  have hb : 10 ≤ r := by omega
  have hm := Nat.mul_le_mul_left r (show 9 ≤ r - 1 by omega)
  nlinarith

/-- A bound attached to each classical syntax, not a bound on field size. -/
def exceptionalPartnerRankBound : RawEntry → ℕ
  | .linear _ _ | .Dminus _ _ => 9
  | .unitary _ _ => 17
  | .B _ _ | .C _ _ | .Dplus _ _ => 8
  | _ => 0

theorem rank_le_exceptionalPartnerRankBound {x : RawEntry} (hx : Admissible x)
    (h : characteristicExponent x ≤ 4 * topIndex x) :
    rankParameter x ≤ exceptionalPartnerRankBound x := by
  cases x with
  | linear d q => exact linear_dimension_le_nine_of_index_ratio hx.1 h
  | unitary d q => exact unitary_dimension_le_seventeen_of_index_ratio hx.1 h
  | B r q | C r q => exact BC_rank_le_eight_of_index_ratio hx.1 h
  | Dplus r q => exact Dplus_rank_le_eight_of_index_ratio hx.1 h
  | Dminus r q => exact Dminus_rank_le_nine_of_index_ratio hx.1 h
  | _ => exact Nat.zero_le _

/-- Transfer the exceptional ratio bound after index and valuation arguments
have supplied the displayed cross-multiplied equality. -/
theorem exponent_le_four_topIndex_of_exceptional_ratio {x y : RawEntry}
    (hy : Admissible y) (hyl : IsLie y) (hye : IsExceptionalLie y)
    (h : characteristicExponent x * topIndex y =
      characteristicExponent y * topIndex x) :
    characteristicExponent x ≤ 4 * topIndex x := by
  have hm := topIndex_two_le hy hyl
  have hb := exceptional_exponent_le_four_topIndex hye
  have ht := Nat.mul_le_mul_right (topIndex x) hb
  apply le_of_mul_le_mul_right (a := topIndex y) _ (by omega)
  nlinarith

theorem rank_bound_of_exceptional_ratio {x y : RawEntry}
    (hx : Admissible x) (hy : Admissible y) (hyl : IsLie y)
    (hye : IsExceptionalLie y)
    (h : characteristicExponent x * topIndex y =
      characteristicExponent y * topIndex x) :
    rankParameter x ≤ exceptionalPartnerRankBound x :=
  rank_le_exceptionalPartnerRankBound hx
    (exponent_le_four_topIndex_of_exceptional_ratio hy hyl hye h)

/-- Eliminate the common positive field-exponent multiplier. -/
theorem index_ratio_of_scaled_equalities {A B M N f g : ℕ}
    (hf : 1 ≤ f) (ha : f * A = g * B) (hm : f * M = g * N) :
    A * N = B * M := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
  calc
    f * (A * N) = (f * A) * N := by ring
    _ = (g * B) * N := by rw [ha]
    _ = (g * N) * B := by ring
    _ = (f * M) * B := by rw [hm]
    _ = f * (B * M) := by ring

/-- The index equality is an explicit hypothesis: the primitive-divisor argument
that should establish it outside the binary exceptional branch is not assumed. -/
theorem index_ratio_of_equal_order_and_top_index {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (hm : f * topIndex x = g * topIndex y) :
    characteristicExponent x * topIndex y =
      characteristicExponent y * topIndex x :=
  index_ratio_of_scaled_equalities hf
    (equal_order_exponents hx hy hlx hly hp hf hg hqx hqy he) hm

theorem rank_bound_of_equal_order_and_top_index {x y : RawEntry} {p f g : ℕ}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hye : IsExceptionalLie y) (hp : p.Prime) (hf : 1 ≤ f) (hg : 1 ≤ g)
    (hqx : fieldSize x = p ^ f) (hqy : fieldSize y = p ^ g)
    (he : order x = order y) (hm : f * topIndex x = g * topIndex y) :
    rankParameter x ≤ exceptionalPartnerRankBound x :=
  rank_bound_of_exceptional_ratio hx hy hly hye
    (index_ratio_of_equal_order_and_top_index hx hy hlx hly hp hf hg hqx hqy he hm)

end Atlas.OrderArithmetic
