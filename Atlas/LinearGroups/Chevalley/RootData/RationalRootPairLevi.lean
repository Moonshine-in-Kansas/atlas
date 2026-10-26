import Atlas.LinearGroups.Chevalley.RootData.RationalZeroRootSupport
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.Tactic.FinCases

/-! The full rational root-pair span is a Weyl translate of a standard
simple-support subspace, of rank at most two and exactly two for distinct
non-opposite roots. The two given roots need not become the two simple roots. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

theorem rationalRootPairSpan_finrank_le_two (i j : ι) :
    Module.finrank ℚ (rationalRootPairSpan P b i j) ≤ 2 := by
  have h := finrank_range_le_card (R := ℚ)
    ![rationalRootCoordinates P b i, rationalRootCoordinates P b j]
  have hr : Set.range ![rationalRootCoordinates P b i, rationalRootCoordinates P b j] =
      {rationalRootCoordinates P b i, rationalRootCoordinates P b j} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm, or_comm]
  rw [hr] at h
  convert h using 1 <;> rfl

/-- Integral independence of distinct non-opposite actual roots remains
independence in the rational simple-root coordinate realization. -/
theorem rationalRootCoordinates_pair_independent (i j : ι)
    (hij : i ≠ j) (hneg : P.root i ≠ -P.root j) :
    LinearIndependent ℚ ![rationalRootCoordinates P b i,
      rationalRootCoordinates P b j] := by
  have hroot := RootPairing.IsReduced.linearIndependent P hij hneg
  have hspan : LinearIndependent ℤ ![P.rootSpanMem ℤ i, P.rootSpanMem ℤ j] := by
    apply LinearIndependent.of_comp (P.rootSpan ℤ).subtype
    convert hroot using 1
    funext k
    fin_cases k <;> rfl
  have hc := hspan.map_injOn b.toWeightBasisInt.equivFun.toLinearMap
    b.toWeightBasisInt.equivFun.injective.injOn
  have hq := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ)).mpr hc
  have heq : (fun k : Fin 2 => (algebraMap ℤ ℚ) ∘
      ((b.toWeightBasisInt.equivFun.toLinearMap) ∘
        ![P.rootSpanMem ℤ i, P.rootSpanMem ℤ j]) k) =
      ![rationalRootCoordinates P b i, rationalRootCoordinates P b j] := by
    funext k t
    fin_cases k <;> rfl
  rw [heq] at hq
  exact hq

theorem rationalRootPairSpan_finrank_eq_two (i j : ι)
    (hij : i ≠ j) (hneg : P.root i ≠ -P.root j) :
    Module.finrank ℚ (rationalRootPairSpan P b i j) = 2 := by
  have h := finrank_span_eq_card (rationalRootCoordinates_pair_independent P b i j hij hneg)
  have hr : Set.range ![rationalRootCoordinates P b i, rationalRootCoordinates P b j] =
      {rationalRootCoordinates P b i, rationalRootCoordinates P b j} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm, or_comm]
  rw [hr] at h
  convert h using 1 <;> rfl

/-- An exact separating functional, after a dominant Weyl translation, identifies
the entire rational pair plane with the image of its zero-simple support span. -/
theorem rationalRootPairSpan_eq_map_zeroSimpleSpan (i j : ι)
    (f : (b.support → ℚ) →ₗ[ℚ] ℚ) (w : P.weylGroupToPerm.range)
    (hzero : ∀ β, f (rationalRootCoordinates P b β) = 0 ↔
      rationalRootCoordinates P b β ∈ rationalRootPairSpan P b i j)
    (hdom : ∀ k : b.support, 0 ≤ f (rationalRootCoordinates P b (w.val k.val))) :
    rationalRootPairSpan P b i j =
      (Pi.spanSubset ℚ (rationalZeroSimpleSet P b
        (f.comp (rationalRootWeylEquiv P b w).toLinearMap) : Set b.support)).map
          (rationalRootWeylEquiv P b w).toLinearMap := by
  let e := rationalRootWeylEquiv P b w
  let g := f.comp e.toLinearMap
  let S := rationalZeroSimpleSet P b g
  have hg : ∀ k : b.support, 0 ≤ g (rationalRootCoordinates P b k.val) := by
    intro k
    simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root] using hdom k
  have hmem (β : ι) :
      rationalRootCoordinates P b (w.val β) ∈ rationalRootPairSpan P b i j ↔
        rationalRootCoordinates P b β ∈ Pi.spanSubset ℚ (S : Set b.support) := by
    rw [← hzero]
    simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root, S] using
      rationalRoot_functional_eq_zero_iff_mem_zeroSimpleSpan P b g hg β
  change rationalRootPairSpan P b i j = (Pi.spanSubset ℚ (S : Set b.support)).map e.toLinearMap
  have hgen (β : ι) (hβ : rationalRootCoordinates P b β ∈ rationalRootPairSpan P b i j) :
      rationalRootCoordinates P b β ∈ (Pi.spanSubset ℚ (S : Set b.support)).map e.toLinearMap := by
    let γ := w.val.symm β
    have hwγ : w.val γ = β := w.val.apply_symm_apply β
    refine Submodule.mem_map.mpr ⟨rationalRootCoordinates P b γ, ?_, ?_⟩
    · exact (hmem γ).mp (by rw [hwγ]; exact hβ)
    · simpa only [e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root, hwγ]
  apply le_antisymm
  · rw [rationalRootPairSpan, Submodule.span_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hgen i (Submodule.subset_span (by simp))
    · have hxj : x = rationalRootCoordinates P b j := Set.mem_singleton_iff.mp hx
      subst x
      exact hgen j (Submodule.subset_span (by simp))
  · rw [Pi.spanSubset, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    have hk0 : g (rationalRootCoordinates P b k.val) = 0 :=
      (Finset.mem_filter.mp hk).2
    rw [← rationalRootCoordinates_simple_eq_basis P b k]
    change e (rationalRootCoordinates P b k.val) ∈ rationalRootPairSpan P b i j
    rw [show e (rationalRootCoordinates P b k.val) =
      rationalRootCoordinates P b (w.val k.val) from rationalRootWeylEquiv_root P b w k.val]
    apply (hzero (w.val k.val)).mp
    simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root] using hk0

/-- Every actual root-pair plane is a Weyl translate of a standard support
subspace with at most two simple directions. The root-label assertion is the
full saturated-plane intersection, not an identification of the pair as simple. -/
theorem exists_rationalRootPair_standardLevi (i j : ι) :
    ∃ w : P.weylGroupToPerm.range, ∃ S : Finset b.support,
      S.card ≤ 2 ∧
      rationalRootPairSpan P b i j =
        (Pi.spanSubset ℚ (S : Set b.support)).map (rationalRootWeylEquiv P b w).toLinearMap ∧
      ∀ β, rationalRootCoordinates P b (w.val β) ∈ rationalRootPairSpan P b i j ↔
        ∀ k ∈ (rootSimpleCoefficients P b β).support, k ∈ S := by
  obtain ⟨f, w, hker, hzero, hdom⟩ := exists_rationalRootPair_dominant_functional P b i j
  let e := rationalRootWeylEquiv P b w
  let g := f.comp e.toLinearMap
  let S := rationalZeroSimpleSet P b g
  have he : rationalRootPairSpan P b i j =
      (Pi.spanSubset ℚ (S : Set b.support)).map e.toLinearMap :=
    rationalRootPairSpan_eq_map_zeroSimpleSpan P b i j f w hzero hdom
  have hdim : Module.finrank ℚ (rationalRootPairSpan P b i j) = S.card := by
    rw [he, e.finrank_map_eq]
    simp only [Pi.dim_spanSubset, Set.ncard_coe_finset]
  refine ⟨w, S, ?_, he, ?_⟩
  · rw [← hdim]
    exact rationalRootPairSpan_finrank_le_two P b i j
  · intro β
    rw [← hzero]
    have hg : ∀ k : b.support, 0 ≤ g (rationalRootCoordinates P b k.val) := by
      intro k
      simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root] using hdom k
    simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root,
      S, rationalZeroSimpleSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      rationalRoot_functional_eq_zero_iff_support P b g hg β

/-- For distinct non-opposite actual roots, the standard support has exactly
two simple directions. This still leaves the positive orientation of the two
original roots and all local group commutator tables to separate arguments. -/
theorem exists_rationalRootPair_rankTwoLevi (i j : ι)
    (hij : i ≠ j) (hneg : P.root i ≠ -P.root j) :
    ∃ w : P.weylGroupToPerm.range, ∃ S : Finset b.support,
      S.card = 2 ∧
      rationalRootPairSpan P b i j =
        (Pi.spanSubset ℚ (S : Set b.support)).map (rationalRootWeylEquiv P b w).toLinearMap ∧
      ∀ β, rationalRootCoordinates P b (w.val β) ∈ rationalRootPairSpan P b i j ↔
        ∀ k ∈ (rootSimpleCoefficients P b β).support, k ∈ S := by
  obtain ⟨w, S, hcard, he, hs⟩ := exists_rationalRootPair_standardLevi P b i j
  refine ⟨w, S, ?_, he, hs⟩
  have hd := congrArg (fun S : Submodule ℚ (b.support → ℚ) => Module.finrank ℚ S) he
  rw [rationalRootPairSpan_finrank_eq_two P b i j hij hneg,
    (rationalRootWeylEquiv P b w).finrank_map_eq] at hd
  simpa only [Pi.dim_spanSubset, Set.ncard_coe_finset] using hd.symm

end Atlas.Chevalley.RootData
