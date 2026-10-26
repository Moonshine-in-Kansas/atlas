import Atlas.LinearGroups.Chevalley.Integral.HeightTriangular
import Atlas.LinearGroups.Chevalley.RootData.RootHeightCombination

/-! Integral heights transported by an actual word of simple reflections.
All root/Cartan transition blocks and all integral divided powers are included. -/

noncomputable section
namespace Atlas.Chevalley.Integral
open RootData

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The actual root-height grading pulled back along a simple-reflection word;
Cartan coordinates retain height zero. -/
def geckWordHeight (l : List b.support) : b.support ⊕ ι → ℤ :=
  Sum.elim (fun _ => 0) (fun a => b.height (simpleReflectionWord P b l a))

/-- A simple raising operator is homogeneous for every transported grading,
with degree the height of the transformed simple root. -/
theorem raising_wordHeight_weightedSupport (l : List b.support) (i : b.support) :
    WeightedSupport (geckWordHeight P b l)
      (b.height (simpleReflectionWord P b l i.val)) (raising P b i) := by
  let := P.indexNeg
  have hneg : b.height (simpleReflectionWord P b l (-i.val)) =
      -b.height (simpleReflectionWord P b l i.val) := by
    have hk : P.root (-i.val) = (-1 : ℤ) • P.root i.val + (0 : ℤ) • P.root i.val := by
      simp only [RootPairing.indexNeg_neg, P.root_reflectionPerm,
        P.reflection_apply_self, neg_one_zsmul, zero_smul, add_zero]
    have he := root_height_zsmul_add P b
      (simpleReflectionWord P b l i.val) (simpleReflectionWord P b l i.val)
      (simpleReflectionWord P b l (-i.val)) (-1) 0
      (simpleReflectionWord_root_zsmul_add P b l i.val i.val (-i.val) (-1) 0 hk)
    simpa only [neg_one_mul, zero_mul, add_zero] using he
  intro row col hne
  rcases row with a | a <;> rcases col with c | c
  · simp [raising, RootPairing.GeckConstruction.e] at hne
  · have hc : c = -i.val := by
      by_contra hc
      simp [raising, RootPairing.GeckConstruction.e, -RootPairing.indexNeg_neg, hc] at hne
    subst c
    simp only [geckWordHeight, Sum.elim_inl, Sum.elim_inr, hneg, neg_add_cancel]
  · have ha : a = i.val := by
      by_contra ha
      simp [raising, RootPairing.GeckConstruction.e, ha] at hne
    subst a
    simp only [geckWordHeight, Sum.elim_inl, Sum.elim_inr, zero_add]
  · have hac : P.root a = P.root i + P.root c := by
      by_contra hac
      simp [raising, RootPairing.GeckConstruction.e, hac] at hne
    have hword := simpleReflectionWord_root_zsmul_add P b l i.val c a 1 1
      (by simpa only [one_smul] using hac)
    have he := root_height_zsmul_add P b
      (simpleReflectionWord P b l i.val) (simpleReflectionWord P b l c)
      (simpleReflectionWord P b l a) 1 1 hword
    simpa only [geckWordHeight, Sum.elim_inr, one_mul, add_comm] using he

/-- Integral cancellation gives the degree of the actual divided-power matrix.
This argument takes place over the integers, before arbitrary base change. -/
theorem raisingDividedPower_wordHeight_weightedSupport
    (l : List b.support) (i : b.support) (n : ℕ) :
    WeightedSupport (geckWordHeight P b l)
      ((n : ℤ) * b.height (simpleReflectionWord P b l i.val))
      (raisingDividedPower P b i n) :=
  (raising_wordHeight_weightedSupport P b l i).divided n
    (factorial_smul_raisingDividedPower P b i n)

variable (R : Type*) [CommRing R]

/-- If the transformed simple root is positive, every positive divided power
vanishes at non-increasing entries of the transported grading. -/
theorem raisingDividedOver_eq_zero_of_wordHeight_le
    (l : List b.support) (i : b.support)
    (hi : b.IsPos (simpleReflectionWord P b l i.val))
    (n : ℕ) (hn : 0 < n) (row col : b.support ⊕ ι)
    (hheight : geckWordHeight P b l row ≤ geckWordHeight P b l col) :
    raisingDividedOver P b R i n row col = 0 := by
  have hd : 0 < b.height (simpleReflectionWord P b l i.val) := b.isPos_iff.mp hi
  have hz : raisingDividedPower P b i n row col = 0 := by
    by_contra hne
    have he := raisingDividedPower_wordHeight_weightedSupport P b l i n row col hne
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hnd := mul_pos hn' hd
    omega
  simp only [raisingDividedOver, Matrix.map_apply, hz, map_zero]

/-- The actual simple root element is unitriangular for any transported grading
in which its transformed root is positive, over every commutative ring. -/
theorem raisingExponential_wordHeightUnitriangular
    (l : List b.support) (i : b.support)
    (hi : b.IsPos (simpleReflectionWord P b l i.val)) (t : R) :
    Atlas.Matrix.HeightUnitriangular (geckWordHeight P b l)
      (raisingExponential P b R i t) := by
  intro row col hheight
  have h1 := raisingDividedOver_eq_zero_of_wordHeight_le P b R l i hi 1 (by decide)
    row col hheight
  have h2 := raisingDividedOver_eq_zero_of_wordHeight_le P b R l i hi 2 (by decide)
    row col hheight
  have h3 := raisingDividedOver_eq_zero_of_wordHeight_le P b R l i hi 3 (by decide)
    row col hheight
  rw [raisingDividedOver_one] at h1
  simp [raisingExponential_expansion, Matrix.add_apply, Matrix.smul_apply, h1, h2, h3]

theorem raisingRootElement_mem_wordHeightUnitriangular
    (l : List b.support) (i : b.support)
    (hi : b.IsPos (simpleReflectionWord P b l i.val)) (t : R) :
    raisingRootElement P b R i t ∈
      Atlas.Matrix.heightUnitriangularSubgroup (geckWordHeight P b l) :=
  ⟨raisingExponential_wordHeightUnitriangular P b R l i hi t,
    raisingExponential_wordHeightUnitriangular P b R l i hi (-t)⟩

end Atlas.Chevalley.Integral
