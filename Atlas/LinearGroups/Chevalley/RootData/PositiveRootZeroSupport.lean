import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-! Nonnegative actual simple-root coefficients and the zero-support criterion
for a dominant additive functional on the integral root lattice. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The actual integral simple-root coefficients, in the pinned lattice basis. -/
def rootSimpleCoefficients (β : ι) : b.support →₀ ℤ :=
  b.toWeightBasisInt.repr (P.rootSpanMem ℤ β)

private theorem rootSpanMem_simple_basis (i : b.support) :
    P.rootSpanMem ℤ i.val = b.toWeightBasisInt i := by
  apply Subtype.ext
  exact (b.coe_toWeightBasisInt_apply i).symm

theorem rootSimpleCoefficients_simple (i : b.support) :
    rootSimpleCoefficients P b i.val = Finsupp.single i 1 := by
  change b.toWeightBasisInt.repr (P.rootSpanMem ℤ i.val) = _
  rw [rootSpanMem_simple_basis]
  exact b.toWeightBasisInt.repr_self i

theorem rootSimpleCoefficients_add (i j k : ι)
    (hroot : P.root k = P.root i + P.root j) :
    rootSimpleCoefficients P b k =
      rootSimpleCoefficients P b i + rootSimpleCoefficients P b j := by
  have h : P.rootSpanMem ℤ k = P.rootSpanMem ℤ i + P.rootSpanMem ℤ j :=
    Subtype.ext hroot
  simp only [rootSimpleCoefficients, h, map_add]

/-- Every coefficient of an actual positive root is a nonnegative integer. -/
theorem rootSimpleCoefficients_nonneg {β : ι} (hβ : b.IsPos β) :
    ∀ i : b.support, 0 ≤ rootSimpleCoefficients P b β i := by
  have hs (i : b.support) : ∀ j : b.support,
      0 ≤ rootSimpleCoefficients P b i.val j := by
    intro j
    rw [rootSimpleCoefficients_simple]
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  refine hβ.induction_on_add (p := fun β => ∀ i : b.support,
    0 ≤ rootSimpleCoefficients P b β i) (fun i hi => hs ⟨i, hi⟩) ?_
  intro i j k hroot hi hj t
  rw [rootSimpleCoefficients_add P b i j k hroot, Finsupp.add_apply]
  exact add_nonneg (hi t) (hs ⟨j, hj⟩ t)

/-- Exact reconstruction inside the actual integral root lattice. -/
theorem rootSimpleCoefficients_sum (β : ι) :
    (∑ i : b.support, rootSimpleCoefficients P b β i • P.rootSpanMem ℤ i.val) =
      P.rootSpanMem ℤ β := by
  simp only [rootSpanMem_simple_basis, rootSimpleCoefficients]
  exact b.toWeightBasisInt.sum_repr (P.rootSpanMem ℤ β)

/-- Evaluate an additive functional on the exact integral root expansion. -/
theorem rootSimpleCoefficients_functional_sum
    (f : P.rootSpan ℤ →+ ℚ) (β : ι) :
    f (P.rootSpanMem ℤ β) =
      ∑ i : b.support, (rootSimpleCoefficients P b β i : ℚ) *
        f (P.rootSpanMem ℤ i.val) := by
  calc
    f (P.rootSpanMem ℤ β) =
        f (∑ i : b.support, rootSimpleCoefficients P b β i •
          P.rootSpanMem ℤ i.val) :=
      congrArg f (rootSimpleCoefficients_sum P b β).symm
    _ = _ := by simp only [map_sum, map_zsmul, zsmul_eq_mul]

/-- A functional nonnegative on actual simple roots is nonnegative on every
positive root. Its domain is the integral lattice, not an assumed Q-module M. -/
theorem positiveRoot_functional_nonneg (f : P.rootSpan ℤ →+ ℚ)
    (hf : ∀ i : b.support, 0 ≤ f (P.rootSpanMem ℤ i.val))
    {β : ι} (hβ : b.IsPos β) : 0 ≤ f (P.rootSpanMem ℤ β) := by
  rw [rootSimpleCoefficients_functional_sum]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Int.cast_nonneg (rootSimpleCoefficients_nonneg P b hβ i)) (hf i)

/-- A positive root has value zero exactly when every simple root occurring
in its actual integral support has value zero. -/
theorem positiveRoot_functional_eq_zero_iff_support (f : P.rootSpan ℤ →+ ℚ)
    (hf : ∀ i : b.support, 0 ≤ f (P.rootSpanMem ℤ i.val))
    {β : ι} (hβ : b.IsPos β) :
    f (P.rootSpanMem ℤ β) = 0 ↔
      ∀ i ∈ (rootSimpleCoefficients P b β).support, f (P.rootSpanMem ℤ i.val) = 0 := by
  have hterm (i : b.support) :
      0 ≤ (rootSimpleCoefficients P b β i : ℚ) * f (P.rootSpanMem ℤ i.val) :=
    mul_nonneg (Int.cast_nonneg (rootSimpleCoefficients_nonneg P b hβ i)) (hf i)
  rw [rootSimpleCoefficients_functional_sum,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)]
  constructor
  · intro hz i hi
    have hcoef : (rootSimpleCoefficients P b β i : ℚ) ≠ 0 :=
      Int.cast_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    exact (mul_eq_zero.mp (hz i (Finset.mem_univ i))).resolve_left hcoef
  · intro hz i hi
    by_cases hcoef : rootSimpleCoefficients P b β i = 0
    · simp only [hcoef, Int.cast_zero, zero_mul]
    · rw [hz i (Finsupp.mem_support_iff.mpr hcoef), mul_zero]

end Atlas.Chevalley.RootData
