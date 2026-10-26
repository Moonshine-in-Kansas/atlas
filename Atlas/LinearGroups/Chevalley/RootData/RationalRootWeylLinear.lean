import Atlas.LinearGroups.Chevalley.RootData.RationalRootPairFunctional
import Atlas.LinearGroups.Chevalley.RootData.PositiveRootZeroSupport
import Mathlib.LinearAlgebra.StdBasis

/-! The actual root-permutation Weyl image acts linearly on rational simple-root
coordinates. The action is verified on every root, using an actual root-pairing
automorphism representing the permutation. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem rationalRootCoordinates_coefficient (β : ι) (i : b.support) :
    rationalRootCoordinates P b β i = (rootSimpleCoefficients P b β i : ℚ) := rfl

theorem rationalRootCoordinates_simple_eq_basis (i : b.support) :
    rationalRootCoordinates P b i.val = Pi.basisFun ℚ b.support i := by
  funext j
  simp only [rationalRootCoordinates_simple, Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- Every actual integral root relation is respected in the rational coordinates. -/
theorem rationalRootCoordinates_of_sum {κ : Type*} [Fintype κ]
    (β : ι) (v : κ → ι) (c : κ → ℤ)
    (h : P.root β = ∑ k, c k • P.root (v k)) :
    rationalRootCoordinates P b β = ∑ k, (c k : ℚ) • rationalRootCoordinates P b (v k) := by
  have hs : P.rootSpanMem ℤ β = ∑ k, c k • P.rootSpanMem ℤ (v k) := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  have hm := congrArg (rationalRootSpanMap P b) hs
  simpa only [map_sum, map_smul, Int.cast_smul_eq_zsmul, rationalRootCoordinates] using hm

/-- Rational linear map with the actual images of the simple roots as columns. -/
def rationalRootWeylLinear (w : P.weylGroupToPerm.range) :
    (b.support → ℚ) →ₗ[ℚ] (b.support → ℚ) :=
  (Pi.basisFun ℚ b.support).constr ℚ
    (fun i => rationalRootCoordinates P b (w.val i.val))

theorem rationalRootWeylLinear_apply (w : P.weylGroupToPerm.range)
    (x : b.support → ℚ) :
    rationalRootWeylLinear P b w x =
      ∑ i : b.support, x i • rationalRootCoordinates P b (w.val i.val) := by
  simp only [rationalRootWeylLinear, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply]

/-- This linear map has the prescribed permutation action on every root,
not just on its simple-root columns. -/
theorem rationalRootWeylLinear_root (w : P.weylGroupToPerm.range) (β : ι) :
    rationalRootWeylLinear P b w (rationalRootCoordinates P b β) =
      rationalRootCoordinates P b (w.val β) := by
  obtain ⟨g, hg⟩ := w.property
  have hgroot (γ : ι) :
      (RootPairing.Equiv.weightHom P g.val) (P.root γ) = P.root (w.val γ) := by
    change g • P.root γ = _
    rw [P.weylGroup_apply_root, hg]
  have hb : P.root β =
      ∑ i : b.support, rootSimpleCoefficients P b β i • P.root i.val := by
    have h := congrArg Subtype.val (rootSimpleCoefficients_sum P b β)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h.symm
  have ht := congrArg (RootPairing.Equiv.weightHom P g.val) hb
  simp only [map_sum, map_smul, hgroot] at ht
  rw [rationalRootWeylLinear_apply]
  simp only [rationalRootCoordinates_coefficient]
  exact (rationalRootCoordinates_of_sum P b (w.val β)
    (fun i : b.support => w.val i.val) (rootSimpleCoefficients P b β) ht).symm

theorem rationalRootWeylLinear_inv_comp (w : P.weylGroupToPerm.range) :
    (rationalRootWeylLinear P b w⁻¹).comp (rationalRootWeylLinear P b w) =
      LinearMap.id := by
  apply (Pi.basisFun ℚ b.support).ext
  intro i
  rw [← rationalRootCoordinates_simple_eq_basis P b i]
  simp only [LinearMap.comp_apply, rationalRootWeylLinear_root, LinearMap.id_apply]
  have hi : (w⁻¹).val (w.val i.val) = i.val := w.val.symm_apply_apply i.val
  rw [hi]

/-- Actual Weyl action as a rational linear equivalence; the inverse is supplied
by the inverse actual root permutation. -/
def rationalRootWeylEquiv (w : P.weylGroupToPerm.range) :
    (b.support → ℚ) ≃ₗ[ℚ] (b.support → ℚ) :=
  LinearEquiv.ofLinearMap (rationalRootWeylLinear P b w)
    (rationalRootWeylLinear P b w⁻¹)
    (by simpa only [inv_inv] using rationalRootWeylLinear_inv_comp P b w⁻¹)
    (rationalRootWeylLinear_inv_comp P b w)

theorem rationalRootWeylEquiv_root (w : P.weylGroupToPerm.range) (β : ι) :
    rationalRootWeylEquiv P b w (rationalRootCoordinates P b β) =
      rationalRootCoordinates P b (w.val β) :=
  rationalRootWeylLinear_root P b w β

end Atlas.Chevalley.RootData
