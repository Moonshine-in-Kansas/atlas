import Atlas.LinearAlgebra.FiniteFunctionalAvoidance
import Atlas.LinearGroups.Chevalley.RootData.DominantRootFunctional

/-! Rational coordinates of the actual integral root lattice and finite
functional avoidance for a saturated root-pair span. The ambient root module
is not assumed to be a rational vector space. -/

noncomputable section
namespace Atlas.Chevalley.RootData
open Classical

variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- Inclusion of the actual integral root lattice in rational simple-root
coordinates, using the already proved integral basis of that lattice. -/
def rationalRootSpanMap : P.rootSpan ℤ →ₗ[ℤ] (b.support → ℚ) where
  toFun x i := (b.toWeightBasisInt.equivFun x i : ℚ)
  map_add' x y := by
    funext i
    simp only [map_add, Pi.add_apply, Int.cast_add]
  map_smul' n x := by
    funext i
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, zsmul_eq_mul, Int.cast_mul]
    rfl

theorem rationalRootSpanMap_injective :
    Function.Injective (rationalRootSpanMap P b) := by
  intro x y h
  apply b.toWeightBasisInt.equivFun.injective
  funext i
  apply Int.cast_injective (α := ℚ)
  exact congrFun h i

/-- Actual root label in rational simple-root coordinates. -/
def rationalRootCoordinates (i : ι) : b.support → ℚ :=
  rationalRootSpanMap P b (P.rootSpanMem ℤ i)

theorem rationalRootCoordinates_injective :
    Function.Injective (rationalRootCoordinates P b) := by
  intro i j h
  have hspan := rationalRootSpanMap_injective P b h
  apply P.root.injective
  exact congrArg Subtype.val hspan

theorem rationalRootCoordinates_opposite (i : ι) :
    rationalRootCoordinates P b (P.reflectionPerm i i) =
      -rationalRootCoordinates P b i := by
  simp only [rationalRootCoordinates, P.rootSpanMem_reflectionPerm_self, map_neg]

theorem rationalRootCoordinates_simple (i : b.support) (j : b.support) :
    rationalRootCoordinates P b i.val j = if i = j then 1 else 0 := by
  have hi : P.rootSpanMem ℤ i.val = b.toWeightBasisInt i := by
    apply Subtype.ext
    exact (b.coe_toWeightBasisInt_apply i).symm
  change (b.toWeightBasisInt.equivFun (P.rootSpanMem ℤ i.val) j : ℚ) = _
  rw [hi, Module.Basis.equivFun_self]
  split_ifs <;> simp

/-- The full rational plane spanned by the two actual roots. Membership of
other root labels in this span is the saturated-root-subsystem condition. -/
def rationalRootPairSpan (i j : ι) : Submodule ℚ (b.support → ℚ) :=
  Submodule.span ℚ {rationalRootCoordinates P b i, rationalRootCoordinates P b j}

/-- One rational linear functional vanishes on the whole pair span and on
exactly those root labels belonging to it. Independence is unnecessary here. -/
theorem exists_rationalRootPair_avoiding_functional (i j : ι) :
    ∃ f : (b.support → ℚ) →ₗ[ℚ] ℚ,
      rationalRootPairSpan P b i j ≤ LinearMap.ker f ∧
      ∀ β, f (rationalRootCoordinates P b β) = 0 ↔
        rationalRootCoordinates P b β ∈ rationalRootPairSpan P b i j :=
  Atlas.LinearAlgebra.exists_linearFunctional_zero_iff_mem
    (rationalRootPairSpan P b i j) (rationalRootCoordinates P b)

/-- The same exact vanishing functional admits an actual Weyl translate
nonnegative on all simple roots. This does not yet identify its zero subsystem
with a standard Levi subsystem. -/
theorem exists_rationalRootPair_dominant_functional (i j : ι) :
    ∃ f : (b.support → ℚ) →ₗ[ℚ] ℚ, ∃ w : P.weylGroupToPerm.range,
      rationalRootPairSpan P b i j ≤ LinearMap.ker f ∧
      (∀ β, f (rationalRootCoordinates P b β) = 0 ↔
        rationalRootCoordinates P b β ∈ rationalRootPairSpan P b i j) ∧
      ∀ k : b.support, 0 ≤ f (rationalRootCoordinates P b (w.val k.val)) := by
  obtain ⟨f, hker, hzero⟩ := exists_rationalRootPair_avoiding_functional P b i j
  obtain ⟨w, hw⟩ := exists_rootWeyl_dominant_functional P b
    (fun β => f (rationalRootCoordinates P b β)) (by
      intro β
      rw [rationalRootCoordinates_opposite, map_neg])
  exact ⟨f, w, hker, hzero, hw⟩

end Atlas.Chevalley.RootData
