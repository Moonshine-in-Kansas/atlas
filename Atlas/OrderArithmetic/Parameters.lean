import Mathlib.Data.Nat.Prime.Int
import Lean.Elab.Tactic.Omega

/-! Pure numerical labels for the order-comparison problem. No group models enter here. -/
namespace Atlas.OrderArithmetic

/-- Numerical field size; witnesses are not part of the label. -/
def PrimePower (q : ℕ) : Prop := ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ q = p ^ f

theorem primePower_two_le {q : ℕ} (h : PrimePower q) : 2 ≤ q := by
  obtain ⟨p, f, hp, hf, rfl⟩ := h
  exact hp.two_le.trans (Nat.le_pow (by omega))

theorem primePower_witness_unique {p r f g : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hf : 1 ≤ f) (hg : 1 ≤ g) (h : p ^ f = r ^ g) : p = r ∧ f = g :=
  hp.pow_inj' hr (by omega) (by omega) h

inductive FixedLabel
  | M11 | M12 | M22 | M23 | M24 | J1 | J2 | J3 | J4 | HS | McL | He | Ru | Suz
  | ON | Co3 | Co2 | Fi22 | HN | Ly | Th | Fi23 | Co1 | Fi24prime | Baby | Monster | Tits
  deriving DecidableEq, Repr

inductive RawEntry
  | cyclic (p : ℕ) | alternating (n : ℕ)
  | linear (d q : ℕ) | unitary (d q : ℕ)
  | B (r q : ℕ) | C (r q : ℕ) | Dplus (r q : ℕ) | Dminus (r q : ℕ)
  | G2 (q : ℕ) | F4 (q : ℕ) | E6 (q : ℕ) | E7 (q : ℕ) | E8 (q : ℕ)
  | twistedE6 (q : ℕ) | trialityD4 (q : ℕ)
  | suzuki (q : ℕ) | smallRee (q : ℕ) | largeRee (q : ℕ)
  | fixed (s : FixedLabel)
  deriving DecidableEq, Repr

/-- The exact simple-label range of the arithmetic specification. -/
def Admissible : RawEntry → Prop
  | .cyclic p => p.Prime
  | .alternating n => 5 ≤ n
  | .linear d q => 2 ≤ d ∧ PrimePower q ∧ ¬ (d = 2 ∧ (q = 2 ∨ q = 3))
  | .unitary d q => 3 ≤ d ∧ PrimePower q ∧ ¬ (d = 3 ∧ q = 2)
  | .B r q | .C r q => 2 ≤ r ∧ PrimePower q ∧ ¬ (r = 2 ∧ q = 2)
  | .Dplus r q | .Dminus r q => 4 ≤ r ∧ PrimePower q
  | .G2 q => PrimePower q ∧ 3 ≤ q
  | .F4 q | .E6 q | .E7 q | .E8 q | .twistedE6 q | .trialityD4 q => PrimePower q
  | .suzuki q | .largeRee q => ∃ m : ℕ, 1 ≤ m ∧ q = 2 ^ (2 * m + 1)
  | .smallRee q => ∃ m : ℕ, 1 ≤ m ∧ q = 3 ^ (2 * m + 1)
  | .fixed _ => True

/-- Separate arithmetic tag for the ordinary Lie formulas. -/
def IsLie : RawEntry → Prop
  | .cyclic _ | .alternating _ | .fixed _ => False
  | _ => True

end Atlas.OrderArithmetic
