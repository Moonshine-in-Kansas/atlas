import Atlas.Algebra.SplitOctonion.Automorphism
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

/-! The quadratic-element geometry in the actual binary split octonions.
A point selects the unique root with coordinate 3 zero from the pair x, 1+x.
Only the 256 algebra elements, never group elements, enter the finite checks. -/
namespace Atlas.Comparisons.G2Binary
open Atlas.SplitOctonion
abbrev K := ZMod 2
abbrev V := Carrier K

def IsQuadraticRoot (x : V) : Prop := trace x = 1 ∧ norm x = 1
instance (x : V) : Decidable (IsQuadraticRoot x) := inferInstanceAs
  (Decidable (trace x = 1 ∧ norm x = 1))
abbrev QuadraticRoot := {x : V // IsQuadraticRoot x}
abbrev QuadraticPoint := {x : V // IsQuadraticRoot x ∧ x 3 = 0}

def partner (x : V) : V := unit + x

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem binary_geometry : ∀ x : V,
    partner (partner x) = x ∧ partner x ≠ x ∧
    (IsQuadraticRoot (partner x) ↔ IsQuadraticRoot x) ∧
    (IsQuadraticRoot x → mul x x + x + unit = 0) := by decide

theorem partner_involutive : Function.Involutive partner := fun x => (binary_geometry x).1

theorem partner_ne (x : V) : partner x ≠ x := (binary_geometry x).2.1

theorem partner_root (x : V) : IsQuadraticRoot (partner x) ↔ IsQuadraticRoot x :=
  (binary_geometry x).2.2.1

theorem root_quadratic_identity (x : QuadraticRoot) :
    mul x.val x.val + x.val + unit = 0 := (binary_geometry x.val).2.2.2 x.property

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem card_quadraticRoot : Fintype.card QuadraticRoot = 56 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem card_quadraticPoint : Fintype.card QuadraticPoint = 28 := by decide

/-- Canonical representative of the unordered pair. -/
def normalize (x : V) : V := if x 3 = 0 then x else partner x

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem normalize_geometry : ∀ x : V,
    (IsQuadraticRoot x → IsQuadraticRoot (normalize x) ∧ normalize x 3 = 0) ∧
    normalize (partner x) = normalize x ∧
    (normalize x = x ∨ normalize x = partner x) := by decide

def pointOfRoot (x : QuadraticRoot) : QuadraticPoint :=
  ⟨normalize x.val, (normalize_geometry x.val).1 x.property⟩

theorem normalize_partner (x : V) : normalize (partner x) = normalize x :=
  (normalize_geometry x).2.1

theorem normalize_cases (x : V) : normalize x = x ∨ normalize x = partner x :=
  (normalize_geometry x).2.2

theorem normalize_eq_iff (x y : V) :
    normalize x = normalize y ↔ x = y ∨ x = partner y := by
  constructor
  · intro h
    rcases normalize_cases x with hx | hx <;> rcases normalize_cases y with hy | hy
    · exact Or.inl (hx.symm.trans (h.trans hy))
    · exact Or.inr (hx.symm.trans (h.trans hy))
    · right
      have he := congrArg partner (hx.symm.trans (h.trans hy))
      simpa only [partner_involutive x, partner_involutive y] using he
    · left
      have he := congrArg partner (hx.symm.trans (h.trans hy))
      simpa only [partner_involutive x, partner_involutive y] using he
  · rintro (rfl | rfl)
    · rfl
    · exact normalize_partner y

end Atlas.Comparisons.G2Binary
