import Atlas.OrderArithmetic.IndexBounds
import Mathlib.NumberTheory.Divisors

namespace Atlas.OrderArithmetic

/-! Field-independent central-divisor candidates for the polynomial comparison
rows. These are bounds for the numerical order formulas, not statements about
centers of constructed groups. -/

/-- Each central denominator divides this fixed family/rank-dependent integer. -/
def centralBound : RawEntry → ℕ
  | .linear d _ | .unitary d _ => d
  | .B _ _ | .C _ _ | .E7 _ => 2
  | .Dplus _ _ | .Dminus _ _ => 4
  | .E6 _ | .twistedE6 _ => 3
  | _ => 1

theorem denominator_dvd_centralBound (x : RawEntry) : denominator x ∣ centralBound x := by
  cases x <;> simp only [denominator, centralBound]
  all_goals first | exact Nat.gcd_dvd_left _ _ | exact dvd_rfl

theorem centralBound_pos {x : RawEntry} (hx : Admissible x) : 0 < centralBound x := by
  cases x with
  | linear d q | unitary d q =>
    have hd := hx.1
    simp only [centralBound]
    omega
  | _ => norm_num [centralBound]

theorem denominator_le_centralBound {x : RawEntry} (hx : Admissible x) :
    denominator x ≤ centralBound x :=
  Nat.le_of_dvd (centralBound_pos hx) (denominator_dvd_centralBound x)

theorem denominator_mem_centralBound_divisors {x : RawEntry} (hx : Admissible x) :
    denominator x ∈ (centralBound x).divisors :=
  Nat.mem_divisors.mpr ⟨denominator_dvd_centralBound x, (centralBound_pos hx).ne'⟩

/-- Replace the field parameter of a Lie-family label. Other labels are retained. -/
def withField : RawEntry → ℕ → RawEntry
  | .linear d _, q => .linear d q
  | .unitary d _, q => .unitary d q
  | .B r _, q => .B r q
  | .C r _, q => .C r q
  | .Dplus r _, q => .Dplus r q
  | .Dminus r _, q => .Dminus r q
  | .G2 _, q => .G2 q
  | .F4 _, q => .F4 q
  | .E6 _, q => .E6 q
  | .E7 _, q => .E7 q
  | .E8 _, q => .E8 q
  | .twistedE6 _, q => .twistedE6 q
  | .trialityD4 _, q => .trialityD4 q
  | .suzuki _, q => .suzuki q
  | .smallRee _, q => .smallRee q
  | .largeRee _, q => .largeRee q
  | x, _ => x

@[simp] theorem withField_id (x : RawEntry) : withField x (fieldSize x) = x := by
  cases x <;> rfl

@[simp] theorem withField_withField (x : RawEntry) (q Q : ℕ) :
    withField (withField x q) Q = withField x Q := by
  cases x <;> rfl

theorem withField_eq_self_of_fieldSize_eq {x : RawEntry} {q : ℕ}
    (hq : fieldSize x = q) : withField x q = x := by
  rw [← hq, withField_id]

theorem fieldSize_withField {x : RawEntry} (hx : IsLie x) (q : ℕ) :
    fieldSize (withField x q) = q := by
  cases x <;> simp_all [IsLie, withField, fieldSize]

@[simp] theorem characteristicExponent_withField (x : RawEntry) (q : ℕ) :
    characteristicExponent (withField x q) = characteristicExponent x := by
  cases x <;> rfl

@[simp] theorem centralBound_withField (x : RawEntry) (q : ℕ) :
    centralBound (withField x q) = centralBound x := by
  cases x <;> rfl

@[simp] theorem topIndex_withField (x : RawEntry) (q : ℕ) :
    topIndex (withField x q) = topIndex x := by
  cases x <;> rfl

@[simp] theorem rankParameter_withField (x : RawEntry) (q : ℕ) :
    rankParameter (withField x q) = rankParameter x := by
  cases x <;> rfl

@[simp] theorem isLie_withField (x : RawEntry) (q : ℕ) :
    IsLie (withField x q) ↔ IsLie x := by
  cases x <;> rfl

@[simp] theorem isExceptionalLie_withField (x : RawEntry) (q : ℕ) :
    IsExceptionalLie (withField x q) ↔ IsExceptionalLie x := by
  cases x <;> rfl

/-- All admissible field substitutions use the same finite divisor set. -/
theorem denominator_withField_mem_divisors {x : RawEntry} {q : ℕ}
    (hx : Admissible (withField x q)) :
    denominator (withField x q) ∈ (centralBound x).divisors := by
  simpa only [centralBound_withField] using denominator_mem_centralBound_divisors hx

end Atlas.OrderArithmetic
