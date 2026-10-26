import Atlas.LinearGroups.Chevalley.Integral.MinusculeRootHeight
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeylWordSupport
import Atlas.LinearAlgebra.HeightUnitriangularConjugate

/-! Positive-root triangularity on each actual minuscule block along a chosen
word of actual Weyl operators, uniformly over commutative coefficient rings. -/

noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)
  (S : Finset (WeightLattice P))
  (hc : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hm : ∀ μ ∈ S, ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)

/-- Pull back the integral weight height by the actual chosen reflection word. -/
def weightWordHeight (l : List b.support) (μ : WeightOrbit P S) : ℤ :=
  weightHeight P b (weightReflectionWord P b l μ.val)

/-- The exact degree is twice the height of the transformed simple root. -/
theorem weightOrbit_raising_wordHeight_weightedSupport
    (l : List b.support) (i : b.support) :
    WeightedSupport (weightWordHeight P b S l)
      (2 * b.height (RootData.simpleReflectionWord P b l i.val))
      ((stringsOfWeightOrbit P S hc hm).stepMatrix ℤ i.val (-1)) := by
  intro μ ν hne
  rw [weightOrbit_stepMatrix_entry] at hne
  have hs : ν.val (corootElement P i.val) = -1 ∧
      weightReflection P i.val ν.val = μ.val := by
    by_contra hs
    simp only [if_neg hs] at hne
    exact hne rfl
  have hμ : μ.val = ν.val + rootWeight P i.val := by
    rw [← hs.2, weightReflection_apply, hs.1]
    simp only [neg_one_smul, sub_neg_eq_add]
  change weightHeight P b (weightReflectionWord P b l μ.val) =
    weightHeight P b (weightReflectionWord P b l ν.val) + _
  rw [hμ, map_add, weightReflectionWord_rootWeight]
  change (weightReflectionWord P b l ν.val +
    rootWeight P (RootData.simpleReflectionWord P b l i.val)) (twiceRhoCoroot P b) = _
  rw [LinearMap.add_apply]
  change weightHeight P b (weightReflectionWord P b l ν.val) +
    weightHeight P b (rootWeight P (RootData.simpleReflectionWord P b l i.val)) = _
  rw [weightHeight_rootWeight]

variable (R : Type*) [CommRing R]

/-- The actual root matrix is unitriangular in every positive transported grading. -/
theorem weightOrbitRootElement_wordHeightUnitriangular
    (l : List b.support) (i : b.support)
    (hi : b.IsPos (RootData.simpleReflectionWord P b l i.val)) (t : R) :
    Atlas.Matrix.HeightUnitriangular (weightWordHeight P b S l)
      (weightOrbitRootElement P S hc hm R i.val (-1) (by decide) t).val := by
  intro μ ν hle
  have hz : (stringsOfWeightOrbit P S hc hm).stepMatrix ℤ i.val (-1) μ ν = 0 := by
    by_contra hne
    have hd := weightOrbit_raising_wordHeight_weightedSupport P b S hc hm l i μ ν hne
    have hp : 0 < b.height (RootData.simpleReflectionWord P b l i.val) := hi
    omega
  have hzero : (stringsOfWeightOrbit P S hc hm).stepMatrix R i.val (-1) μ ν = 0 := by
    rw [weightOrbit_stepMatrix_entry] at hz ⊢
    by_cases hs : ν.val (corootElement P i.val) = -1 ∧
        weightReflection P i.val ν.val = μ.val
    · rw [if_pos hs] at hz
      exact False.elim (one_ne_zero hz)
    · exact if_neg hs
  change (1 + t • (stringsOfWeightOrbit P S hc hm).stepMatrix R i.val (-1)) μ ν = _
  simp only [Matrix.add_apply, Matrix.smul_apply, hzero, smul_zero, add_zero]

theorem weightOrbitWeylWord_weightHeight_support (l : List b.support)
    (μ ν : WeightOrbit P S)
    (hne : (weightOrbitWeylWord P b S hc hm R l).val μ ν ≠ 0) :
    weightHeight P b μ.val = weightWordHeight P b S l ν := by
  rw [weightOrbitWeylWord_support P b S hc hm R l μ ν hne]
  rw [weightOrbitReflectionWord_val]
  rfl

theorem weightOrbitWeylWord_inv_weightHeight_support (l : List b.support)
    (μ ν : WeightOrbit P S)
    (hne : ((weightOrbitWeylWord P b S hc hm R l)⁻¹).val μ ν ≠ 0) :
    weightWordHeight P b S l μ = weightHeight P b ν.val := by
  have he := weightOrbitWeylWord_inv_support P b S hc hm R l μ ν hne
  change weightHeight P b (weightReflectionWord P b l μ.val) = _
  rw [← weightOrbitReflectionWord_val P b S hc l μ, he]
  rw [Equiv.Perm.inv_def, (weightOrbitReflectionWord P b S hc l).apply_symm_apply]

/-- The conjugate of a simple root family along a positive-root word is
unitriangular on this entire minuscule block, not just on selected entries. -/
theorem weightOrbitWeylWord_conjugate_root_heightUnitriangular
    (l : List b.support) (i : b.support)
    (hi : b.IsPos (RootData.simpleReflectionWord P b l i.val)) (t : R) :
    Atlas.Matrix.HeightUnitriangular
      (fun μ : WeightOrbit P S => weightHeight P b μ.val)
      (weightOrbitWeylWord P b S hc hm R l *
        weightOrbitRootElement P S hc hm R i.val (-1) (by decide) t *
          (weightOrbitWeylWord P b S hc hm R l)⁻¹).val := by
  apply Atlas.Matrix.HeightUnitriangular.conj_of_height_transport
    (weightOrbitRootElement_wordHeightUnitriangular P b S hc hm R l i hi t)
    (weightOrbitWeylWord_weightHeight_support P b S hc hm R l)
    (weightOrbitWeylWord_inv_weightHeight_support P b S hc hm R l)
  exact (weightOrbitWeylWord P b S hc hm R l).val_inv

end Atlas.Chevalley.Integral.Minuscule
