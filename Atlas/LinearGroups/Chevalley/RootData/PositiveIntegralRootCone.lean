import Atlas.LinearGroups.Chevalley.RootData.RationalRootWeylLinear
import Atlas.LinearGroups.Chevalley.RootData.RootHeightCombination
import Mathlib.Tactic.Linarith

/-! Strict positive integral cones of actual root labels, expressed in the
faithful rational simple-root coordinates. Weyl transport preserves the same
integer coefficients, so local factors increase the original positive height. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Rational coordinate equality detects the actual integral root relation;
no rational vector-space structure on the ambient root module is assumed. -/
theorem rationalRootCoordinates_zsmul_add_iff
    (α β γ : ι) (a c : ℤ) :
    rationalRootCoordinates P b γ =
      (a : ℚ) • rationalRootCoordinates P b α +
        (c : ℚ) • rationalRootCoordinates P b β ↔
      P.root γ = a • P.root α + c • P.root β := by
  constructor
  · intro h
    have hs : P.rootSpanMem ℤ γ =
        a • P.rootSpanMem ℤ α + c • P.rootSpanMem ℤ β := by
      apply rationalRootSpanMap_injective P b
      simpa only [map_add, map_smul, Int.cast_smul_eq_zsmul,
        rationalRootCoordinates] using h
    have hv := congrArg Subtype.val hs
    simpa only [Submodule.coe_add, Submodule.coe_smul] using hv
  · intro h
    have hs : P.rootSpanMem ℤ γ =
        a • P.rootSpanMem ℤ α + c • P.rootSpanMem ℤ β := Subtype.ext h
    have hm := congrArg (rationalRootSpanMap P b) hs
    simpa only [map_add, map_smul, Int.cast_smul_eq_zsmul,
      rationalRootCoordinates] using hm

/-- An actual Weyl element transports a coordinate relation without changing
its coefficients. The two input roots need not be simple. -/
theorem rationalRootCoordinates_combination_weyl
    (w : P.weylGroupToPerm.range) (α β γ : ι) (a c : ℚ)
    (h : rationalRootCoordinates P b γ =
      a • rationalRootCoordinates P b α + c • rationalRootCoordinates P b β) :
    rationalRootCoordinates P b (w.val γ) =
      a • rationalRootCoordinates P b (w.val α) +
        c • rationalRootCoordinates P b (w.val β) := by
  have hw := congrArg (rationalRootWeylEquiv P b w) h
  simpa only [map_add, map_smul, rationalRootWeylEquiv_root] using hw

/-- The output root is a strictly positive integral combination of both
input roots. This says more than membership in their rational plane. -/
def PositiveIntegralRootCone (α β γ : ι) : Prop :=
  ∃ a c : ℕ, 0 < a ∧ 0 < c ∧
    rationalRootCoordinates P b γ =
      (a : ℚ) • rationalRootCoordinates P b α +
        (c : ℚ) • rationalRootCoordinates P b β

theorem positiveIntegralRootCone_of_root_eq
    (α β γ : ι) (a c : ℕ) (ha : 0 < a) (hc : 0 < c)
    (h : P.root γ = (a : ℤ) • P.root α + (c : ℤ) • P.root β) :
    PositiveIntegralRootCone P b α β γ := by
  refine ⟨a, c, ha, hc, ?_⟩
  simpa only [Int.cast_natCast] using
    (rationalRootCoordinates_zsmul_add_iff P b α β γ a c).mpr h

/-- The coordinate predicate is exactly the literal actual-root statement. -/
theorem positiveIntegralRootCone_iff_root_eq (α β γ : ι) :
    PositiveIntegralRootCone P b α β γ ↔
      ∃ a c : ℕ, 0 < a ∧ 0 < c ∧
        P.root γ = (a : ℤ) • P.root α + (c : ℤ) • P.root β := by
  constructor
  · rintro ⟨a, c, ha, hc, h⟩
    refine ⟨a, c, ha, hc, (rationalRootCoordinates_zsmul_add_iff P b α β γ a c).mp ?_⟩
    simpa only [Int.cast_natCast] using h
  · rintro ⟨a, c, ha, hc, h⟩
    exact positiveIntegralRootCone_of_root_eq P b α β γ a c ha hc h

theorem positiveIntegralRootCone_comm (α β γ : ι) :
    PositiveIntegralRootCone P b α β γ ↔ PositiveIntegralRootCone P b β α γ := by
  constructor <;> rintro ⟨a, c, ha, hc, h⟩
  · exact ⟨c, a, hc, ha, h.trans (add_comm _ _)⟩
  · exact ⟨c, a, hc, ha, h.trans (add_comm _ _)⟩

/-- Actual root permutation transport retains the same positive integral
coefficients. This is independent of normalizer lifts and group kernels. -/
theorem positiveIntegralRootCone_weyl (w : P.weylGroupToPerm.range)
    {α β γ : ι} (h : PositiveIntegralRootCone P b α β γ) :
    PositiveIntegralRootCone P b (w.val α) (w.val β) (w.val γ) := by
  obtain ⟨a, c, ha, hc, he⟩ := h
  exact ⟨a, c, ha, hc,
    rationalRootCoordinates_combination_weyl P b w α β γ a c he⟩

theorem positiveIntegralRootCone_weyl_iff (w : P.weylGroupToPerm.range)
    (α β γ : ι) :
    PositiveIntegralRootCone P b (w.val α) (w.val β) (w.val γ) ↔
      PositiveIntegralRootCone P b α β γ := by
  constructor
  · intro h
    have hi := positiveIntegralRootCone_weyl P b w⁻¹ h
    have hα : (w⁻¹).val (w.val α) = α := w.val.symm_apply_apply α
    have hβ : (w⁻¹).val (w.val β) = β := w.val.symm_apply_apply β
    have hγ : (w⁻¹).val (w.val γ) = γ := w.val.symm_apply_apply γ
    simpa only [hα, hβ, hγ] using hi
  · exact positiveIntegralRootCone_weyl P b w

/-- A commutator output in the strict cone has larger height than each
original positive input, not merely larger height in a local rank-two chart. -/
theorem positiveIntegralRootCone_height_gt {α β γ : ι}
    (h : PositiveIntegralRootCone P b α β γ) (hα : b.IsPos α) (hβ : b.IsPos β) :
    b.height α < b.height γ ∧ b.height β < b.height γ := by
  obtain ⟨a, c, ha, hc, he⟩ := (positiveIntegralRootCone_iff_root_eq P b α β γ).mp h
  have hh := root_height_zsmul_add P b α β γ a c he
  have haZ : (1 : ℤ) ≤ a := by omega
  have hcZ : (1 : ℤ) ≤ c := by omega
  have hαZ : 0 < b.height α := hα
  have hβZ : 0 < b.height β := hβ
  have hleft := mul_le_mul_of_nonneg_right haZ (le_of_lt hαZ)
  have hright := mul_le_mul_of_nonneg_right hcZ (le_of_lt hβZ)
  constructor <;> nlinarith

theorem positiveIntegralRootCone_isPos {α β γ : ι}
    (h : PositiveIntegralRootCone P b α β γ) (hα : b.IsPos α) (hβ : b.IsPos β) :
    b.IsPos γ :=
  lt_trans hα (positiveIntegralRootCone_height_gt P b h hα hβ).1

/-- Local cone identities imply strict original-height growth after any
actual Weyl transport whose two input images are positive. -/
theorem positiveIntegralRootCone_weyl_height_gt
    (w : P.weylGroupToPerm.range) {α β γ : ι}
    (h : PositiveIntegralRootCone P b α β γ)
    (hα : b.IsPos (w.val α)) (hβ : b.IsPos (w.val β)) :
    b.height (w.val α) < b.height (w.val γ) ∧
      b.height (w.val β) < b.height (w.val γ) :=
  positiveIntegralRootCone_height_gt P b (positiveIntegralRootCone_weyl P b w h) hα hβ

end Atlas.Chevalley.RootData
