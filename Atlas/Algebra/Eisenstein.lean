import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Algebra
open scoped QuadraticAlgebra

/-- Integral scalar algebra with ω²+ω+1=0. -/
abbrev Eisenstein := QuadraticAlgebra ℤ (-1) (-1)

def eisensteinOmega : Eisenstein := QuadraticAlgebra.omega

def eisensteinTheta : Eisenstein := 1 + 2 * eisensteinOmega

theorem eisenstein_relation : eisensteinOmega ^ 2 + eisensteinOmega + 1 = 0 := by
  ext <;> norm_num [eisensteinOmega, QuadraticAlgebra.omega, pow_two]

theorem eisenstein_cube : eisensteinOmega ^ 3 = 1 := by
  ext <;> norm_num [eisensteinOmega, QuadraticAlgebra.omega, pow_succ]

theorem eisensteinTheta_sq : eisensteinTheta ^ 2 = -3 := by
  ext <;> norm_num [eisensteinTheta, eisensteinOmega, QuadraticAlgebra.omega, pow_two]

theorem eisenstein_conjugate : star eisensteinOmega = -1 - eisensteinOmega := by
  ext <;> norm_num [eisensteinOmega, QuadraticAlgebra.omega]

theorem eisenstein_norm (z : Eisenstein) :
    z.norm = z.re ^ 2 - z.re * z.im + z.im ^ 2 := by
  simp [QuadraticAlgebra.norm_def]; ring

theorem eisenstein_norm_nonneg (z : Eisenstein) : 0 ≤ z.norm := by
  rw [eisenstein_norm]
  nlinarith [sq_nonneg (2*z.re-z.im), sq_nonneg z.im]

theorem eisenstein_norm_one_iff (z : Eisenstein) : z.norm = 1 ↔
    z = 1 ∨ z = -1 ∨ z = eisensteinOmega ∨ z = -eisensteinOmega ∨
      z = 1 + eisensteinOmega ∨ z = -1 - eisensteinOmega := by
  constructor
  · intro h
    rw [eisenstein_norm] at h
    have hi : -1 ≤ z.im ∧ z.im ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (2*z.re-z.im)]
    have hr : -1 ≤ z.re ∧ z.re ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (2*z.im-z.re)]
    rcases z with ⟨r,i⟩
    dsimp at *
    obtain ⟨hir, his⟩ := hi
    obtain ⟨hrr, hrs⟩ := hr
    interval_cases r <;> interval_cases i <;>
      norm_num [eisensteinOmega, QuadraticAlgebra.omega, QuadraticAlgebra.ext_iff] at *
  · rintro (rfl|rfl|rfl|rfl|rfl|rfl) <;>
      norm_num [eisenstein_norm, eisensteinOmega, QuadraticAlgebra.omega]

theorem eisenstein_isUnit_iff (z : Eisenstein) : IsUnit z ↔ z.norm = 1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, Int.isUnit_iff]
  have h := eisenstein_norm_nonneg z
  omega

/-- Reduction modulo θ sends ω to 1 over F3. -/
def eisensteinResidue : Eisenstein →+* ZMod 3 where
  toFun z := (z.re : ZMod 3) + (z.im : ZMod 3)
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intros; simp; ring
  map_mul' := by
    intro z w
    simp
    have h3 : (3 : ZMod 3) = 0 := by decide
    linear_combination -(z.im : ZMod 3) * (w.im : ZMod 3) * h3

theorem eisensteinResidue_surjective : Function.Surjective eisensteinResidue := by
  intro x
  refine ⟨⟨x.val, 0⟩, ?_⟩
  simp [eisensteinResidue]


theorem eisensteinResidue_eq_zero (z : Eisenstein) :
    eisensteinResidue z = 0 ↔ eisensteinTheta ∣ z := by
  change ((z.re : ZMod 3) + (z.im : ZMod 3) = 0) ↔ _
  rw [← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨⟨z.im-k, z.im-2*k⟩, ?_⟩
    ext <;> simp [eisensteinTheta, eisensteinOmega, QuadraticAlgebra.omega] <;> omega
  · rintro ⟨w, rfl⟩
    refine ⟨w.re-w.im, ?_⟩
    simp [eisensteinTheta, eisensteinOmega, QuadraticAlgebra.omega]
    ring

theorem eisensteinResidue_ker : RingHom.ker eisensteinResidue =
    Ideal.span {eisensteinTheta} := by
  ext z
  exact (eisensteinResidue_eq_zero z).trans Ideal.mem_span_singleton.symm

/-- The actual residue field comparison, not just its cardinality. -/
noncomputable def eisensteinResidueEquiv :
    Eisenstein ⧸ Ideal.span {eisensteinTheta} ≃+* ZMod 3 :=
  (Ideal.quotEquivOfEq eisensteinResidue_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective eisensteinResidue_surjective)

def eisensteinUnitValues : Finset Eisenstein :=
  {1, -1, eisensteinOmega, -eisensteinOmega, 1+eisensteinOmega, -1-eisensteinOmega}

theorem eisenstein_mem_unitValues (z : Eisenstein) :
    z ∈ eisensteinUnitValues ↔ IsUnit z := by
  simp only [eisensteinUnitValues, Finset.mem_insert, Finset.mem_singleton]
  exact (eisenstein_norm_one_iff z).symm.trans (eisenstein_isUnit_iff z).symm

theorem eisensteinUnitValues_card : eisensteinUnitValues.card = 6 := by decide +kernel

noncomputable def eisensteinUnitsEquiv : Eisensteinˣ ≃ eisensteinUnitValues :=
  Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv.trans
    (Equiv.subtypeEquivRight (fun z => (eisenstein_mem_unitValues z).symm))

theorem eisenstein_units_card : Nat.card Eisensteinˣ = 6 := by
  rw [Nat.card_congr eisensteinUnitsEquiv, Nat.card_eq_fintype_card,
    Fintype.card_coe, eisensteinUnitValues_card]
end Atlas.Algebra
