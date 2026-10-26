import Atlas.OrderArithmetic.SecondIndexBounds
import Mathlib.Tactic.Ring

namespace Atlas.OrderArithmetic

/-! Symbolic classification of the two numerical classical index invariants.
The indices remain numerical tables, independently of the outstanding proof of
their cyclotomic interpretation. No equality of group orders is used here. -/

/-- Shifted parameters enforce the classical lower-rank bounds and separate the
unitary parity cases without natural-number subtraction in the profiles. -/
inductive ClassicalIndexProfile
  | linear (k : ℕ)
  | unitaryOdd (k : ℕ)
  | unitaryEven (k : ℕ)
  | unitaryFour
  | BC (k : ℕ)
  | Dplus (k : ℕ)
  | Dminus (k : ℕ)
  deriving DecidableEq

namespace ClassicalIndexProfile

def top : ClassicalIndexProfile → ℕ
  | .linear k => k + 2
  | .unitaryOdd k => 4 * k + 6
  | .unitaryEven k => 4 * k + 10
  | .unitaryFour => 6
  | .BC k => 2 * k + 4
  | .Dplus k => 2 * k + 6
  | .Dminus k => 2 * k + 8

def second : ClassicalIndexProfile → ℕ
  | .linear k => k + 1
  | .unitaryOdd k => 4 * k + 2
  | .unitaryEven k => 4 * k + 6
  | .unitaryFour => 4
  | .BC k => 2 * k + 2
  | .Dplus k => 2 * k + 4
  | .Dminus k => 2 * k + 6

/-- Twice the characteristic exponent. -/
def twiceExponent : ClassicalIndexProfile → ℕ
  | .linear k => (k + 2) * (k + 1)
  | .unitaryOdd k => (2 * k + 3) * (2 * k + 2)
  | .unitaryEven k => (2 * k + 6) * (2 * k + 5)
  | .unitaryFour => 12
  | .BC k => 2 * (k + 2) ^ 2
  | .Dplus k | .Dminus k => 2 * (k + 4) * (k + 3)

/-- The integer value of twice `top / (top - second)`. -/
def doubleRatio : ClassicalIndexProfile → ℕ
  | .linear k | .BC k => 2 * k + 4
  | .unitaryOdd k => 2 * k + 3
  | .unitaryEven k => 2 * k + 5
  | .unitaryFour => 6
  | .Dplus k => 2 * k + 6
  | .Dminus k => 2 * k + 8

/-- Only the symbolic coincidences listed in the arithmetic specification. -/
def Compatible : ClassicalIndexProfile → ClassicalIndexProfile → Prop
  | .linear k, .linear l | .unitaryOdd k, .unitaryOdd l
      | .unitaryEven k, .unitaryEven l | .BC k, .BC l
      | .Dplus k, .Dplus l | .Dminus k, .Dminus l => k = l
  | .unitaryFour, .unitaryFour => True
  | .linear k, .unitaryFour | .unitaryFour, .linear k => k = 1
  | .linear k, .Dminus l | .Dminus l, .linear k => k = l + 2
  | _, _ => False

theorem doubleRatio_eq_of_second_cross {x y : ClassicalIndexProfile}
    (h : x.second * y.top = y.second * x.top) : x.doubleRatio = y.doubleRatio := by
  cases x <;> cases y <;> simp only [second, top, doubleRatio] at * <;> nlinarith

/-- Exact classification of the pair of numerical profiles, at arbitrary rank. -/
theorem compatible_of_two_cross_equalities {x y : ClassicalIndexProfile}
    (ha : x.twiceExponent * y.top = y.twiceExponent * x.top)
    (hs : x.second * y.top = y.second * x.top) : Compatible x y := by
  have hr := doubleRatio_eq_of_second_cross hs
  cases x <;> cases y <;>
    simp only [twiceExponent, top, doubleRatio, Compatible] at ha hr ⊢
  all_goals solve
    | omega
    | (rename_i k l
       have he : k = l := by omega
       subst k
       ring_nf at ha
       omega)
    | (rename_i k l
       have he : k = l + 1 := by omega
       subst k
       ring_nf at ha
       omega)
    | (rename_i k l
       have he : k = l + 2 := by omega
       subst k
       ring_nf at ha
       omega)
    | (rename_i k l
       have he : l = k + 1 := by omega
       subst l
       ring_nf at ha
       omega)
    | (rename_i k l
       have he : l = k + 2 := by omega
       subst l
       ring_nf at ha
       omega)
    | (rename_i k
       have he : k = 0 := by omega
       subst k
       norm_num at ha)
    | (rename_i k
       have he : k = 1 := by omega
       subst k
       norm_num at ha)
    | (rename_i k
       have he : k = 2 := by omega
       subst k
       norm_num at ha)

theorem compatible_alternatives {p r : ClassicalIndexProfile} (h : Compatible p r) :
    p = r ∨
    (p = .linear 1 ∧ r = .unitaryFour) ∨
    (p = .unitaryFour ∧ r = .linear 1) ∨
    (∃ k, p = .linear (k + 2) ∧ r = .Dminus k) ∨
    (∃ k, p = .Dminus k ∧ r = .linear (k + 2)) := by
  cases p <;> cases r <;> simp_all [Compatible]

end ClassicalIndexProfile

/-- A profile represents a family and rank, with no constraint on the field size. -/
def ClassicalIndexProfile.Represents : ClassicalIndexProfile → RawEntry → Prop
  | .linear k, x => ∃ q, x = .linear (k + 2) q
  | .unitaryOdd k, x => ∃ q, x = .unitary (2 * k + 3) q
  | .unitaryEven k, x => ∃ q, x = .unitary (2 * k + 6) q
  | .unitaryFour, x => ∃ q, x = .unitary 4 q
  | .BC k, x => ∃ q, x = .B (k + 2) q ∨ x = .C (k + 2) q
  | .Dplus k, x => ∃ q, x = .Dplus (k + 4) q
  | .Dminus k, x => ∃ q, x = .Dminus (k + 4) q

theorem exists_classicalIndexProfile {x : RawEntry} (hx : Admissible x)
    (hc : IsClassicalLie x) : ∃ p : ClassicalIndexProfile, p.Represents x := by
  cases x with
  | linear d q =>
    have hd := hx.1
    refine ⟨.linear (d - 2), q, ?_⟩
    congr 1
    omega
  | unitary d q =>
    have hd : 3 ≤ d := hx.1
    by_cases h4 : d = 4
    · exact ⟨.unitaryFour, q, by subst d; rfl⟩
    rcases Nat.even_or_odd d with he | ho
    · obtain ⟨t, ht⟩ := he
      refine ⟨.unitaryEven (t - 3), q, ?_⟩
      congr 1
      omega
    · obtain ⟨t, ht⟩ := ho
      refine ⟨.unitaryOdd (t - 1), q, ?_⟩
      congr 1
      omega
  | B r q =>
    have hr := hx.1
    refine ⟨.BC (r - 2), q, Or.inl ?_⟩
    congr 1
    omega
  | C r q =>
    have hr := hx.1
    refine ⟨.BC (r - 2), q, Or.inr ?_⟩
    congr 1
    omega
  | Dplus r q =>
    have hr := hx.1
    refine ⟨.Dplus (r - 4), q, ?_⟩
    congr 1
    omega
  | Dminus r q =>
    have hr := hx.1
    refine ⟨.Dminus (r - 4), q, ?_⟩
    congr 1
    omega
  | _ => simp_all [IsClassicalLie]

private theorem twice_triangular (d : ℕ) :
    2 * (d * (d - 1) / 2) = d * (d - 1) := by
  simpa only [mul_comm 2] using Nat.div_mul_cancel (Nat.even_mul_pred_self d).two_dvd

theorem ClassicalIndexProfile.Represents.top_eq {p : ClassicalIndexProfile} {x : RawEntry}
    (h : p.Represents x) : topIndex x = p.top := by
  cases p with
  | linear k | Dplus k | Dminus k =>
    obtain ⟨q, rfl⟩ := h
    simp [topIndex, ClassicalIndexProfile.top] <;> omega
  | BC k =>
    obtain ⟨q, h | h⟩ := h <;> subst x <;>
      simp [topIndex, ClassicalIndexProfile.top] <;> omega
  | unitaryOdd k =>
    obtain ⟨q, rfl⟩ := h
    have he : ¬ Even (2 * k + 3) := by rw [Nat.even_iff]; omega
    simp [topIndex, ClassicalIndexProfile.top, he]
    omega
  | unitaryEven k =>
    obtain ⟨q, rfl⟩ := h
    have he : Even (2 * k + 6) := by rw [Nat.even_iff]; omega
    simp [topIndex, ClassicalIndexProfile.top, he]
    omega
  | unitaryFour =>
    obtain ⟨q, rfl⟩ := h
    have he : Even (4 : ℕ) := ⟨2, rfl⟩
    simp [topIndex, ClassicalIndexProfile.top, he]

theorem ClassicalIndexProfile.Represents.second_eq {p : ClassicalIndexProfile} {x : RawEntry}
    (h : p.Represents x) : secondIndex x = p.second := by
  cases p with
  | linear k | Dplus k | Dminus k =>
    obtain ⟨q, rfl⟩ := h
    simp [secondIndex, ClassicalIndexProfile.second] <;> omega
  | BC k =>
    obtain ⟨q, h | h⟩ := h <;> subst x <;>
      simp [secondIndex, ClassicalIndexProfile.second] <;> omega
  | unitaryOdd k =>
    obtain ⟨q, rfl⟩ := h
    have he : ¬ Even (2 * k + 3) := by rw [Nat.even_iff]; omega
    simp only [secondIndex, ClassicalIndexProfile.second, if_neg he]
    split_ifs <;> omega
  | unitaryEven k =>
    obtain ⟨q, rfl⟩ := h
    have he : Even (2 * k + 6) := by rw [Nat.even_iff]; omega
    simp only [secondIndex, ClassicalIndexProfile.second, if_pos he]
    split_ifs <;> omega
  | unitaryFour =>
    obtain ⟨q, rfl⟩ := h
    norm_num [secondIndex, ClassicalIndexProfile.second]

theorem ClassicalIndexProfile.Represents.twiceExponent_eq {p : ClassicalIndexProfile}
    {x : RawEntry} (h : p.Represents x) : 2 * characteristicExponent x = p.twiceExponent := by
  cases p with
  | linear k | unitaryOdd k | unitaryEven k =>
    obtain ⟨q, rfl⟩ := h
    simp only [characteristicExponent, twice_triangular, ClassicalIndexProfile.twiceExponent]
    congr 1 <;> omega
  | BC k =>
    obtain ⟨q, h | h⟩ := h <;> subst x <;> rfl
  | Dplus k | Dminus k =>
    obtain ⟨q, rfl⟩ := h
    simp only [characteristicExponent, ClassicalIndexProfile.twiceExponent]
    have hs : k + 4 - 1 = k + 3 := by omega
    rw [hs]
    ring
  | unitaryFour =>
    obtain ⟨q, rfl⟩ := h
    norm_num [characteristicExponent, ClassicalIndexProfile.twiceExponent]

/-- The complete symbolic alternatives, expressed through the explicit profile
representations above. They concern family/rank syntax only, not field transport. -/
def ClassicalInvariantCompatible (x y : RawEntry) : Prop :=
  ∃ p r : ClassicalIndexProfile, p.Represents x ∧ r.Represents y ∧
    ClassicalIndexProfile.Compatible p r

theorem classicalInvariantCompatible_of_cross_equalities {x y : RawEntry}
    (hx : Admissible x) (hy : Admissible y)
    (hcx : IsClassicalLie x) (hcy : IsClassicalLie y)
    (ha : characteristicExponent x * topIndex y =
      characteristicExponent y * topIndex x)
    (hs : secondIndex x * topIndex y = secondIndex y * topIndex x) :
    ClassicalInvariantCompatible x y := by
  obtain ⟨p, hp⟩ := exists_classicalIndexProfile hx hcx
  obtain ⟨r, hr⟩ := exists_classicalIndexProfile hy hcy
  refine ⟨p, r, hp, hr, ClassicalIndexProfile.compatible_of_two_cross_equalities ?_ ?_⟩
  · rw [← hp.twiceExponent_eq, ← hr.twiceExponent_eq, ← hp.top_eq, ← hr.top_eq]
    nlinarith
  · simpa only [hp.top_eq, hr.top_eq, hp.second_eq, hr.second_eq] using hs

end Atlas.OrderArithmetic
