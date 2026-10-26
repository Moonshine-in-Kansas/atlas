import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.Dual.Basis

/-! Actual full weight lattice as the integral dual of Q∨.
This reuses the pinned integral simple-coroot basis. No rational base change,
selected orbit, lattice quotient order, or group-level statement is assumed. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule
open Classical

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) (b : P.Base)

/-- The actual integral span of all coroots in the existing ambient lattice. -/
abbrev CorootLattice := P.flip.rootSpan ℤ

/-- The full weight lattice is the integral dual of the coroot lattice. -/
abbrev WeightLattice := Module.Dual ℤ (CorootLattice P)

/-- The pinned base API already proves the simple coroots form an integral basis. -/
def corootBasis : Module.Basis b.support ℤ (CorootLattice P) :=
  b.flip.toWeightBasisInt

/-- Fundamental weights, defined literally as the basis dual to the simple coroots. -/
def fundamentalWeights : Module.Basis b.support ℤ (WeightLattice P) :=
  (corootBasis P b).dualBasis

/-- Integral fundamental-weight coordinates are exact simple-coroot evaluations. -/
def weightCoordinates : WeightLattice P ≃ₗ[ℤ] (b.support → ℤ) :=
  (fundamentalWeights P b).equivFun

@[simp] theorem weightCoordinates_apply (μ : WeightLattice P) (i : b.support) :
    weightCoordinates P b μ i = μ (corootBasis P b i) := by
  exact (corootBasis P b).dualBasis_equivFun μ i

@[simp] theorem fundamentalWeights_pairing (i j : b.support) :
    fundamentalWeights P b i (corootBasis P b j) = if j = i then 1 else 0 := by
  exact (corootBasis P b).dualBasis_apply_self i j

/-- An actual root defines a weight by restriction of its pairing to Q∨. -/
def rootWeight (i : ι) : WeightLattice P :=
  (P.toLinearMap (P.root i)).comp (P.flip.rootSpan ℤ).subtype

/-- The root's fundamental-weight coordinates are its genuine coroot pairings. -/
theorem rootWeight_coordinates (i : ι) (j : b.support) :
    weightCoordinates P b (rootWeight P i) j = P.pairing i j := by
  rw [weightCoordinates_apply]
  change P.toLinearMap (P.root i) ((b.flip.toWeightBasisInt j : P.flip.rootSpan ℤ) : N) = _
  exact congrArg (P.toLinearMap (P.root i))
    (b.flip.coe_toWeightBasisInt_apply (⟨j.val, j.property⟩ : b.flip.support))

variable [P.IsCrystallographic]

/-- In particular the simple-root coordinate rows are exactly the pinned Cartan matrix. -/
theorem simpleRootWeight_coordinates (i j : b.support) :
    weightCoordinates P b (rootWeight P i) j = b.cartanMatrix i j := by
  rw [rootWeight_coordinates]
  exact (P.algebraMap_pairingIn ℤ i j).symm

/-- Actual coroot as an element of its integral span. -/
def corootElement (i : ι) : CorootLattice P := P.flip.rootSpanMem ℤ i

@[simp] theorem rootWeight_corootElement (i j : ι) :
    rootWeight P i (corootElement P j) = P.pairing i j := rfl

/-- Reflection of a weight in Q∨-dual form, with integral coefficients throughout. -/
def weightReflection (i : ι) : WeightLattice P →ₗ[ℤ] WeightLattice P where
  toFun μ := μ - μ (corootElement P i) • rootWeight P i
  map_add' μ ν := by simp only [LinearMap.add_apply, add_smul]; abel
  map_smul' t μ := by simp only [LinearMap.smul_apply, smul_sub, smul_smul, smul_eq_mul, RingHom.id_apply]

@[simp] theorem weightReflection_apply (i : ι) (μ : WeightLattice P) :
    weightReflection P i μ = μ - μ (corootElement P i) • rootWeight P i := rfl

/-- Its evaluation on the reflecting coroot reverses sign. -/
theorem weightReflection_grade (i : ι) (μ : WeightLattice P) :
    weightReflection P i μ (corootElement P i) = -μ (corootElement P i) := by
  simp only [weightReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, rootWeight_corootElement, P.pairing_same]
  ring

/-- Integral reflection is involutive; no weight-lattice denominator was introduced. -/
theorem weightReflection_involutive (i : ι) : Function.Involutive (weightReflection P i) := by
  intro μ
  rw [weightReflection_apply, weightReflection_grade, weightReflection_apply]
  simp

/-- The actual root lattice inside the full integral weight lattice. -/
def rootLattice : Submodule ℤ (WeightLattice P) :=
  Submodule.span ℤ (Set.range (rootWeight P))

theorem rootWeight_mem_rootLattice (i : ι) : rootWeight P i ∈ rootLattice P :=
  Submodule.subset_span ⟨i, rfl⟩

/-- The integral weight reflection agrees with the existing actual root reflection. -/
theorem weightReflection_rootWeight (i j : ι) :
    weightReflection P i (rootWeight P j) = rootWeight P (P.reflectionPerm i j) := by
  rw [weightReflection_apply, rootWeight_corootElement]
  ext x
  change P.toLinearMap (P.root j) x.val - P.pairing j i * P.toLinearMap (P.root i) x.val =
    P.toLinearMap (P.root (P.reflectionPerm i j)) x.val
  rw [P.root_reflectionPerm, P.reflection_apply_root]
  simp

end Atlas.Chevalley.Integral.Minuscule
