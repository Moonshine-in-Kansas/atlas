import Atlas.LinearGroups.Symplectic.Center
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.OrderOfElement

/-! # Actual projective symplectic involution lifts and signed conjugacy -/
noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

def negativeIdentity : Sp n F := scalarElement ⟨(-1 : Fˣ),by simp⟩

@[simp] theorem negativeIdentity_apply (x : Vector n F) :
    (negativeIdentity : Sp n F) • x = -x := by
  simp [negativeIdentity,scalarElement_apply]

theorem negativeIdentity_central : (negativeIdentity : Sp n F) ∈ Subgroup.center (Sp n F) :=
  scalar_is_central _ (-1) (by intro x; simpa using negativeIdentity_apply x)

@[simp] theorem negativeIdentity_square : (negativeIdentity : Sp n F)^2 = 1 := by
  apply ext_action
  intro x
  simp [pow_two,mul_smul]

@[simp] theorem projection_negativeIdentity : projection (negativeIdentity : Sp n F) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr negativeIdentity_central

/-- The actual center consists precisely of the two scalar matrices. -/
theorem center_iff_eq_one_or_negativeIdentity (hn : 0 < n) (g : Sp n F) :
    g ∈ Subgroup.center (Sp n F) ↔ g = 1 ∨ g = negativeIdentity := by
  constructor
  · intro hg
    obtain ⟨a,ha,hga⟩ := (mem_center_iff_scalar hn g).mp hg
    rcases sq_eq_one_iff.mp ha with ha | ha
    · left
      apply ext_action
      intro x
      simp [hga,ha]
    · right
      apply ext_action
      intro x
      simp [hga,ha]
  · rintro (rfl|rfl)
    · exact (Subgroup.center _).one_mem
    · exact negativeIdentity_central

/-- An actual lift of a projective square-one element squares to I or -I. -/
theorem projection_square_eq_one_iff (hn : 0 < n) (g : Sp n F) :
    (projection g)^2 = 1 ↔ g^2 = 1 ∨ g^2 = negativeIdentity := by
  rw [← map_pow]
  change (QuotientGroup.mk (g^2) : PSp n F) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff,center_iff_eq_one_or_negativeIdentity hn]

/-- Projective equality is precisely equality up to the actual central sign. -/
theorem projection_eq_iff_signed (hn : 0 < n) (g h : Sp n F) :
    projection g = projection h ↔ g = h ∨ g = negativeIdentity * h := by
  constructor
  · intro he
    have hz : projection (g*h⁻¹) = 1 := by rw [map_mul,map_inv,he,mul_inv_cancel]
    have hc : g*h⁻¹ ∈ Subgroup.center (Sp n F) := (QuotientGroup.eq_one_iff _).mp hz
    rcases (center_iff_eq_one_or_negativeIdentity hn _).mp hc with hh|hh
    · exact Or.inl (mul_inv_eq_one.mp hh)
    · right
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun z => z*h) hh
  · rintro (rfl|rfl)
    · rfl
    · rw [map_mul,projection_negativeIdentity,one_mul]

/-- Projective conjugacy is exactly actual symplectic conjugacy up to the central sign. -/
theorem projection_isConj_iff_signed (hn : 0 < n) (g h : Sp n F) :
    IsConj (projection g) (projection h) ↔ IsConj g h ∨ IsConj g (negativeIdentity*h) := by
  simp only [isConj_iff]
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨b,rfl⟩ := projection_surjective a
    have hh : projection (b*g*b⁻¹) = projection h := by simpa using ha
    rcases (projection_eq_iff_signed hn _ _).mp hh with hh|hh
    · exact Or.inl ⟨b,hh⟩
    · exact Or.inr ⟨b,hh⟩
  · rintro (⟨a,ha⟩|⟨a,ha⟩)
    · exact ⟨projection a,by simpa using congrArg projection ha⟩
    · exact ⟨projection a,by simpa using congrArg projection ha⟩

theorem negativeIdentity_ne_one (hn : 0 < n) (h2 : (2 : F) ≠ 0) :
    (negativeIdentity : Sp n F) ≠ 1 := by
  intro he
  let i : Fin n := ⟨0,hn⟩
  have hh := congrArg (fun g : Sp n F => (g • e (F := F) i) (.inl i)) he
  have hc : (-1 : F) = 1 := by simpa [e] using hh
  apply h2
  linear_combination -hc

/-- The lift criterion excludes precisely the central elements, so the identity class is never counted. -/
theorem projection_order_two_iff (hn : 0 < n) (g : Sp n F) :
    orderOf (projection g) = 2 ↔
      (g^2 = 1 ∨ g^2 = negativeIdentity) ∧ g ≠ 1 ∧ g ≠ negativeIdentity := by
  rw [orderOf_eq_prime_iff,projection_square_eq_one_iff hn]
  have he : projection g ≠ 1 ↔ g ≠ 1 ∧ g ≠ negativeIdentity := by
    rw [← map_one projection]
    simp only [ne_eq,projection_eq_iff_signed hn g 1,mul_one,not_or]
  rw [he]

end Atlas.Symplectic
