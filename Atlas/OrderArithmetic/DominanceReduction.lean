import Atlas.OrderArithmetic.HighRankCharacteristic
import Atlas.OrderArithmetic.HighRankDOrthogonal
import Atlas.OrderArithmetic.ExceptionalHighDominance
import Atlas.OrderArithmetic.E6Dominance
import Atlas.OrderArithmetic.G2Dominance
import Atlas.OrderArithmetic.F4Dominance
import Atlas.OrderArithmetic.SuzukiDominance
import Atlas.OrderArithmetic.SmallReeDominance
import Atlas.OrderArithmetic.LargeReeDominance
import Atlas.OrderArithmetic.TrialityDominance
import Atlas.OrderArithmetic.IndexBounds

namespace Atlas.OrderArithmetic

/-- Every exceptional-family numerical order has strict characteristic
dominance. This theorem concerns the integer formulas, not constructed groups. -/
theorem exceptional_characteristic_dominance {x : RawEntry} {l : ℕ}
    (hx : Admissible x) (he : IsExceptionalLie x) (hl : l.Prime)
    (hlq : ¬ l ∣ fieldSize x) :
    l ^ (order x).factorization l < fieldSize x ^ characteristicExponent x := by
  cases x with
  | G2 q => exact g2_cross_contribution_lt hx hl hlq
  | F4 q => exact F4_cross_contribution_lt hx hl hlq
  | E6 q => exact E6_cross_contribution_lt hx hl hlq
  | E7 q => exact E7_cross_contribution_lt hx hl hlq
  | E8 q => exact E8_cross_contribution_lt hx hl hlq
  | twistedE6 q => exact twistedE6_cross_contribution_lt hx hl hlq
  | trialityD4 q => exact trialityD4_cross_contribution_lt hx hl hlq
  | suzuki q =>
    apply suzuki_cross_contribution_lt hx hl
    intro h
    subst l
    obtain ⟨m, hm, rfl⟩ := hx
    exact hlq (dvd_pow_self 2 (by omega))
  | smallRee q =>
    apply smallRee_cross_contribution_lt hx hl
    intro h
    subst l
    obtain ⟨m, hm, rfl⟩ := hx
    exact hlq (dvd_pow_self 3 (by omega))
  | largeRee q =>
    apply largeRee_cross_contribution_lt hx hl
    intro h
    subst l
    obtain ⟨m, hm, rfl⟩ := hx
    exact hlq (dvd_pow_self 2 (by omega))
  | _ => simp_all [IsExceptionalLie]

/-- The remaining ranks in the characteristic-dominance proof. Field sizes
are still unbounded; membership does not assert an actual failure. -/
def SmallClassicalDominanceRange : RawEntry → Prop
  | .linear d _ => d < 8
  | .unitary d _ => d < 10
  | .B r _ | .C r _ => r < 5
  | .Dplus r _ | .Dminus r _ => r < 6
  | _ => False

/-- Any failure of strict characteristic dominance lies in the explicit
small classical ranks. There is no bound on the field parameter. -/
theorem dominance_failure_small_classical {x : RawEntry} {l : ℕ}
    (hx : Admissible x) (hLie : IsLie x) (hl : l.Prime)
    (hlq : ¬ l ∣ fieldSize x)
    (hlarge : fieldSize x ^ characteristicExponent x ≤ l ^ (order x).factorization l) :
    SmallClassicalDominanceRange x := by
  have hnex : ¬ IsExceptionalLie x := by
    intro he
    exact (not_lt_of_ge hlarge) (exceptional_characteristic_dominance hx he hl hlq)
  cases x with
  | linear d q =>
    change d < 8
    by_contra hd
    exact (not_lt_of_ge hlarge)
      (linear_cross_contribution_lt_of_eight_le hx (by omega) hl hlq)
  | unitary d q =>
    change d < 10
    by_contra hd
    exact (not_lt_of_ge hlarge)
      (unitary_cross_contribution_lt_of_ten_le hx (by omega) hl hlq)
  | B r q =>
    change r < 5
    by_contra hr
    exact (not_lt_of_ge hlarge)
      (odd_orthogonal_cross_contribution_lt_of_five_le hx (by omega) hl hlq)
  | C r q =>
    change r < 5
    by_contra hr
    exact (not_lt_of_ge hlarge)
      (symplectic_cross_contribution_lt_of_five_le hx (by omega) hl hlq)
  | Dplus r q =>
    change r < 6
    by_contra hr
    exact (not_lt_of_ge hlarge)
      (split_orthogonal_cross_contribution_lt_of_six_le hx (by omega) hl hlq)
  | Dminus r q =>
    change r < 6
    by_contra hr
    exact (not_lt_of_ge hlarge)
      (minus_orthogonal_cross_contribution_lt_of_six_le hx (by omega) hl hlq)
  | _ => simp_all [IsLie, IsExceptionalLie]

end Atlas.OrderArithmetic
