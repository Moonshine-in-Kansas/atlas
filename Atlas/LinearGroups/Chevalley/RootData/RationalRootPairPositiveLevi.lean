import Atlas.LinearGroups.Chevalley.RootData.RationalRootPairLevi
import Atlas.LinearGroups.Chevalley.RootData.LexDominantRootFunctional

/-! Lexicographic dominance orients the entire saturated rank-two root subsystem.
The original pair may remain non-simple inside that subsystem. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

private theorem height_root_opposite (β : ι) :
    b.height (P.reflectionPerm β β) = -b.height β :=
  b.height_reflectionPerm_self β

/-- The sum of actual rational simple coordinates is the original integral height. -/
theorem rationalRootCoordinates_sumCoords (β : ι) :
    (Pi.basisFun ℚ b.support).sumCoords (rationalRootCoordinates P b β) =
      (b.height β : ℚ) := by
  have hs (i : b.support) :
      (Pi.basisFun ℚ b.support).sumCoords (rationalRootCoordinates P b i.val) =
        (b.height i.val : ℚ) := by
    rw [rationalRootCoordinates_simple_eq_basis, Module.Basis.sumCoords_self_apply,
      b.height_one_of_mem_support i.property]
    rfl
  have hp (γ : ι) (hγ : b.IsPos γ) :
      (Pi.basisFun ℚ b.support).sumCoords (rationalRootCoordinates P b γ) =
        (b.height γ : ℚ) := by
    refine hγ.induction_on_add (p := fun γ =>
      (Pi.basisFun ℚ b.support).sumCoords (rationalRootCoordinates P b γ) =
        (b.height γ : ℚ)) (fun i hi => hs ⟨i, hi⟩) ?_
    intro i j k hk hi hj
    have hc : rationalRootCoordinates P b k =
        rationalRootCoordinates P b i + rationalRootCoordinates P b j := by
      have hr : P.rootSpanMem ℤ k = P.rootSpanMem ℤ i + P.rootSpanMem ℤ j :=
        Subtype.ext hk
      simp only [rationalRootCoordinates, hr, map_add]
    rw [hc, map_add, hi, hs ⟨j, hj⟩, b.height_add hk, Int.cast_add]
  rcases RootPairing.Base.IsPos.or_neg b β with hpos | hneg
  · exact hp β hpos
  · have h := hp (P.reflectionPerm β β) hneg
    simpa only [rationalRootCoordinates_opposite, map_neg,
      height_root_opposite P b, Int.cast_neg, neg_inj] using h

/-- On the zero-root subsystem, a lexicographically dominant Weyl translate
preserves positivity. The secondary functional is the original root height. -/
theorem rootWeyl_isPos_iff_on_zero_subsystem
    (f : (b.support → ℚ) →ₗ[ℚ] ℚ) (w : P.weylGroupToPerm.range)
    (hw : ∀ k : b.support,
      0 ≤ f (rationalRootCoordinates P b (w.val k.val)) ∧
      (f (rationalRootCoordinates P b (w.val k.val)) = 0 →
        0 ≤ (b.height (w.val k.val) : ℚ)))
    (β : ι) (hβ : f (rationalRootCoordinates P b (w.val β)) = 0) :
    b.IsPos (w.val β) ↔ b.IsPos β := by
  let e := rationalRootWeylEquiv P b w
  let g := f.comp e.toLinearMap
  let H := (Pi.basisFun ℚ b.support).sumCoords.comp e.toLinearMap
  have hg : ∀ k : b.support, 0 ≤ g (rationalRootCoordinates P b k.val) := by
    intro k
    simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root] using (hw k).1
  have hnonneg (γ : ι) (hγ : b.IsPos γ)
      (hz : f (rationalRootCoordinates P b (w.val γ)) = 0) :
      0 ≤ (b.height (w.val γ) : ℚ) := by
    have hgz : g (rationalRootCoordinates P b γ) = 0 := by
      simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root] using hz
    have hsupport := (rationalRoot_functional_eq_zero_iff_support P b g hg γ).mp hgz
    have hsum := rootSimpleCoefficients_functional_sum P b
      (H.toAddMonoidHom.comp (rationalRootSpanMap P b).toAddMonoidHom) γ
    change H (rationalRootCoordinates P b γ) =
      ∑ k : b.support, (rootSimpleCoefficients P b γ k : ℚ) *
        H (rationalRootCoordinates P b k.val) at hsum
    have hn : 0 ≤ H (rationalRootCoordinates P b γ) := by
      rw [hsum]
      apply Finset.sum_nonneg
      intro k hk
      by_cases hc : rootSimpleCoefficients P b γ k = 0
      · rw [hc, Int.cast_zero, zero_mul]
      · apply mul_nonneg (Int.cast_nonneg (rootSimpleCoefficients_nonneg P b hγ k))
        have hk0 := hsupport k (Finsupp.mem_support_iff.mpr hc)
        have hkf : f (rationalRootCoordinates P b (w.val k.val)) = 0 := by
          simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root] using hk0
        simpa only [H, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root,
          rationalRootCoordinates_sumCoords] using (hw k).2 hkf
    simpa only [H, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root,
      rationalRootCoordinates_sumCoords] using hn
  constructor
  · intro hpos
    rcases RootPairing.Base.IsPos.or_neg b β with hposβ | hnegβ
    · exact hposβ
    · have hz : f (rationalRootCoordinates P b
          (w.val (P.reflectionPerm β β))) = 0 := by
        rw [rootWeyl_apply_opposite P b, rationalRootCoordinates_opposite, map_neg,
          hβ, neg_zero]
      have hn := hnonneg (P.reflectionPerm β β) hnegβ hz
      rw [rootWeyl_apply_opposite P b, height_root_opposite P b, Int.cast_neg] at hn
      have hp : 0 < (b.height (w.val β) : ℚ) :=
        Int.cast_pos.mpr ((b.isPos_iff).mp hpos)
      linarith
  · intro hpos
    exact (b.isPos_iff').mpr (Int.cast_nonneg_iff.mp (hnonneg β hpos hβ))

/-- The full saturated pair-plane is a standard rank-two subsystem after an
actual Weyl transport, and this transport preserves exactly its positive roots. -/
theorem exists_rationalRootPair_positive_rankTwoLevi (i j : ι)
    (hij : i ≠ j) (hneg : P.root i ≠ -P.root j) :
    ∃ w : P.weylGroupToPerm.range, ∃ S : Finset b.support,
      S.card = 2 ∧
      rationalRootPairSpan P b i j =
        (Pi.spanSubset ℚ (S : Set b.support)).map (rationalRootWeylEquiv P b w).toLinearMap ∧
      (∀ β, rationalRootCoordinates P b (w.val β) ∈ rationalRootPairSpan P b i j ↔
        ∀ k ∈ (rootSimpleCoefficients P b β).support, k ∈ S) ∧
      ∀ β, rationalRootCoordinates P b (w.val β) ∈ rationalRootPairSpan P b i j →
        (b.IsPos (w.val β) ↔ b.IsPos β) := by
  obtain ⟨f, hker, hzero⟩ := exists_rationalRootPair_avoiding_functional P b i j
  obtain ⟨w, hw⟩ := exists_rootWeyl_lex_dominant_functionals P b
    (fun β => f (rationalRootCoordinates P b β)) (fun β => (b.height β : ℚ))
    (by intro β; rw [rationalRootCoordinates_opposite, map_neg])
    (by intro β; rw [height_root_opposite P b, Int.cast_neg])
  let e := rationalRootWeylEquiv P b w
  let g := f.comp e.toLinearMap
  let S := rationalZeroSimpleSet P b g
  have hdom : ∀ k : b.support, 0 ≤ f (rationalRootCoordinates P b (w.val k.val)) :=
    fun k => (hw k).1
  have he : rationalRootPairSpan P b i j =
      (Pi.spanSubset ℚ (S : Set b.support)).map e.toLinearMap :=
    rationalRootPairSpan_eq_map_zeroSimpleSpan P b i j f w hzero hdom
  have hdim : S.card = 2 := by
    have hd := congrArg (fun S : Submodule ℚ (b.support → ℚ) => Module.finrank ℚ S) he
    rw [rationalRootPairSpan_finrank_eq_two P b i j hij hneg, e.finrank_map_eq] at hd
    simpa only [Pi.dim_spanSubset, Set.ncard_coe_finset] using hd.symm
  refine ⟨w, S, hdim, he, ?_, ?_⟩
  · intro β
    rw [← hzero]
    have hg : ∀ k : b.support, 0 ≤ g (rationalRootCoordinates P b k.val) := by
      intro k
      simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root] using hdom k
    simpa only [g, LinearMap.comp_apply, e, LinearEquiv.coe_coe, rationalRootWeylEquiv_root,
      S, rationalZeroSimpleSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      rationalRoot_functional_eq_zero_iff_support P b g hg β
  · intro β hβ
    exact rootWeyl_isPos_iff_on_zero_subsystem P b f w hw β ((hzero (w.val β)).mpr hβ)

end Atlas.Chevalley.RootData
