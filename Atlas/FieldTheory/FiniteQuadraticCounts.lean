import Atlas.FieldTheory.FiniteQuadraticExtension
import Mathlib.GroupTheory.Index

/-! # Trace fibres and norm-one units in a finite quadratic extension -/
noncomputable section
namespace Atlas.FiniteQuadratic
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Norm-one units, as a subgroup of the actual extension's unit group. -/
def normOne : Subgroup Kˣ := (Units.map (norm F K)).ker

instance normOne_cyclic : IsCyclic (normOne F K) := inferInstance

variable {F K}
theorem trace_kernel_finrank (hdeg : Module.finrank F K = 2) :
    Module.finrank F (trace F K).ker = 1 := by
  have h := (trace F K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (trace_surjective F K), finrank_top,
    Module.finrank_self, hdeg] at h
  omega

theorem trace_kernel_card (hdeg : Module.finrank F K = 2) :
    Nat.card (trace F K).ker = Nat.card F := by
  rw [Module.natCard_eq_pow_finrank (K := F), trace_kernel_finrank hdeg, pow_one]

theorem trace_fiber_card (hdeg : Module.finrank F K = 2) (a : F) :
    Nat.card {x : K // trace F K x = a} = Nat.card F := by
  obtain ⟨b, hb⟩ := trace_surjective F K a
  let e : {x : K // trace F K x = a} ≃ (trace F K).ker := {
    toFun := fun x => ⟨x.val - b, by simp [LinearMap.mem_ker, map_sub, x.prop, hb]⟩
    invFun := fun x => ⟨x.val + b, by simp [map_add, hb]⟩
    left_inv := fun x => Subtype.ext (sub_add_cancel x.val b)
    right_inv := fun x => Subtype.ext (add_sub_cancel_right x.val b) }
  exact (Nat.card_congr e).trans (trace_kernel_card hdeg)


theorem normOne_card (hdeg : Module.finrank F K = 2) :
    Nat.card (normOne F K) = Nat.card F + 1 := by
  have h := (normOne F K).card_mul_index
  have hr : (Units.map (norm F K)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (norm_units_surjective F K)
  change Nat.card (normOne F K) * (Units.map (norm F K)).ker.index = Nat.card Kˣ at h
  rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_units, Nat.card_units,
    card_extension hdeg] at h
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hs := Nat.sub_add_cancel (show 1 ≤ Nat.card F by omega)
  have hs2 := Nat.sub_add_cancel (show 1 ≤ Nat.card F ^ 2 by nlinarith)
  nlinarith

/-- The trace-zero parameters are exactly those required by unitary transvections. -/
theorem trace_zero_iff (hdeg : Module.finrank F K = 2) (x : K) :
    trace F K x = 0 ↔ x + conjugation F K x = 0 := by
  rw [← trace_formula hdeg]
  exact ((algebraMap F K).injective.eq_iff' (map_zero _)).symm

theorem exists_nonzero_trace_zero (hdeg : Module.finrank F K = 2) :
    ∃ x : K, x ≠ 0 ∧ x + conjugation F K x = 0 := by
  have hc : 1 < Nat.card (trace F K).ker := by
    rw [trace_kernel_card hdeg]
    exact Finite.one_lt_card
  have : Nontrivial (trace F K).ker := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨x, hx⟩ := exists_ne (0 : (trace F K).ker)
  refine ⟨x, ?_, (trace_zero_iff hdeg x).mp x.prop⟩
  intro he
  exact hx (Subtype.ext he)
theorem normOne_mem_iff (hdeg : Module.finrank F K = 2) (u : Kˣ) :
    u ∈ normOne F K ↔ (u : K) * conjugation F K (u : K) = 1 := by
  change Units.map (norm F K) u = 1 ↔ _
  rw [Units.ext_iff]
  change norm F K (u : K) = 1 ↔ _
  rw [← norm_formula hdeg]
  exact ((algebraMap F K).injective.eq_iff' (map_one _)).symm

theorem norm_zero_iff (hdeg : Module.finrank F K = 2) (x : K) :
    norm F K x = 0 ↔ x = 0 := by
  rw [← (algebraMap F K).injective.eq_iff, map_zero, norm_formula hdeg]
  simp only [mul_eq_zero, map_eq_zero, or_self]

theorem norm_units_fiber_card (hdeg : Module.finrank F K = 2) (a : Fˣ) :
    Nat.card {x : Kˣ // Units.map (norm F K) x = a} = Nat.card F + 1 := by
  let f := Units.map (norm F K)
  obtain ⟨b, hb⟩ := norm_units_surjective F K a
  let e : {x : Kˣ // f x = a} ≃ normOne F K := {
    toFun := fun x => ⟨x.val * b⁻¹, by
      change f (x.val * b⁻¹) = 1
      rw [map_mul, map_inv, x.prop, hb, mul_inv_cancel]⟩
    invFun := fun x => ⟨x.val * b, by
      rw [map_mul, show f x.val = 1 from x.prop, hb, one_mul]⟩
    left_inv := fun x => Subtype.ext (by group)
    right_inv := fun x => Subtype.ext (by group) }
  exact (Nat.card_congr e).trans (normOne_card hdeg)
end Atlas.FiniteQuadratic

