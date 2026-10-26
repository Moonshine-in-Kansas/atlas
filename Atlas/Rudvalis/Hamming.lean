import Atlas.Rudvalis.Coordinates
import Atlas.Codes.BinaryLift
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace Atlas.Rudvalis
open scoped BigOperators

abbrev BinaryWord := Coordinate → Bit
abbrev BinaryParameters := (Point → Bit) × (Matrix (Fin 3) (Fin 3) Bit) × E

def matrixAt (M : Matrix (Fin 3) (Fin 3) Bit) (p : E) : E :=
  fun j => ∑ i, M j i * p i

/-- The literal normal form of Version 33, equation binarynormal. -/
def binaryNormalMap : BinaryParameters →ₗ[Bit] BinaryWord where
  toFun a := fun z => a.1 z.1 + dot (matrixAt a.2.1 z.1.val) z.2 + theta z.1 a.2.2 z.2
  map_add' := by
    intro a b
    funext z
    simp [theta, quadratic, dot, eta, matrixAt, Fin.sum_univ_succ]
    ring
  map_smul' := by
    intro a b
    funext z
    simp [theta, quadratic, dot, eta, matrixAt, Fin.sum_univ_succ]
    ring

def binaryResidue : Submodule Bit BinaryWord := binaryNormalMap.range

/-- Uniqueness of seven Boolean polynomial coefficients on a single cube.
Only 128 coefficient choices are checked; the 2^19-word code is not enumerated. -/
theorem affine_quadratic_zero (a : Bit) (b c : E)
    (h : ∀ x, a + dot b x + quadratic c x = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel +revert

def basisPoint (i : Fin 3) : Point :=
  ⟨binaryLabel (![1,2,4] i), by fin_cases i <;> decide⟩

theorem binaryNormalMap_injective : Function.Injective binaryNormalMap := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  have h (p : Point) : a.1 p = 0 ∧ matrixAt a.2.1 p.val + eta p a.2.2 = 0 ∧ a.2.2 = 0 := by
    apply affine_quadratic_zero
    intro x
    have hx := congrFun ha (p,x)
    change a.1 p + dot (matrixAt a.2.1 p.val) x + theta p a.2.2 x = 0 at hx
    simpa [theta, dot_add_left, add_assoc, add_comm, add_left_comm] using hx
  have hc : a.2.2 = 0 := (h (basisPoint 0)).2.2
  have hm : a.2.1 = 0 := by
    funext j i
    have hi := congrFun (h (basisPoint i)).2.1 j
    rw [hc] at hi
    fin_cases i <;>
      simpa [basisPoint, binaryLabel, matrixAt, eta, Fin.sum_univ_succ] using hi
  exact Prod.ext (funext fun p => (h p).1) (Prod.ext hm hc)

theorem binaryResidue_finrank : Module.finrank Bit binaryResidue = 19 := by
  rw [binaryResidue, LinearMap.finrank_range_of_inj binaryNormalMap_injective]
  change Module.finrank Bit ((Point → Bit) × (Fin 3 → Fin 3 → Bit) × E) = 19
  rw [Module.finrank_prod, Module.finrank_prod]
  simp [E, Module.finrank_pi_fintype]

/-- The torsion layer is defined as the actual orthogonal code. -/
def binaryTorsion : Submodule Bit BinaryWord :=
  (Atlas.Codes.binaryDot (ι := Coordinate)).orthogonal binaryResidue

theorem binaryTorsion_finrank : Module.finrank Bit binaryTorsion = 37 := by
  rw [binaryTorsion, LinearMap.BilinForm.finrank_orthogonal
    Atlas.Codes.binaryDot_nondegenerate, binaryResidue_finrank]
  have h : Module.finrank Bit BinaryWord = 56 := by
    simp [BinaryWord]
  rw [h]

theorem binaryResidue_unique_normal_form (w : BinaryWord) :
    w ∈ binaryResidue ↔ ∃! a, binaryNormalMap a = w := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,ha,fun b hb => binaryNormalMap_injective (hb.trans ha.symm)⟩
  · rintro ⟨a,ha,_⟩
    exact ⟨a,ha⟩

abbrev BinaryGeneratorIndex := Point ⊕ ((Fin 3 × Fin 3) ⊕ Fin 3)

def binaryParameterGenerator : BinaryGeneratorIndex → BinaryParameters
  | .inl p => (Pi.single p 1, 0, 0)
  | .inr (.inl (j,i)) => (0, Pi.single j (Pi.single i 1), 0)
  | .inr (.inr i) => (0, 0, Pi.single i 1)

def binaryParameterCoefficient (a : BinaryParameters) : BinaryGeneratorIndex → Bit
  | .inl p => a.1 p
  | .inr (.inl (j,i)) => a.2.1 j i
  | .inr (.inr i) => a.2.2 i

theorem binaryParameter_expansion (a : BinaryParameters) :
    ∑ i, binaryParameterCoefficient a i • binaryParameterGenerator i = a := by
  classical
  apply Prod.ext
  · ext p
    simp [binaryParameterCoefficient, binaryParameterGenerator, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Pi.single_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
  · apply Prod.ext
    · ext j i
      simp [binaryParameterCoefficient, binaryParameterGenerator, Fintype.sum_sum_type,
        Fintype.sum_prod_type, Pi.single_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
      change (∑ u : Fin 3, ∑ v : Fin 3, a.2.1 u v *
        ((Pi.single u (Pi.single v 1) : Matrix (Fin 3) (Fin 3) Bit) j i)) = a.2.1 j i
      simp [Pi.single_apply, ite_apply, mul_ite]
    · ext i
      simp [binaryParameterCoefficient, binaryParameterGenerator, Fintype.sum_sum_type,
        Fintype.sum_prod_type, Pi.single_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

theorem binaryNormalMap_expansion (a : BinaryParameters) :
    binaryNormalMap a = ∑ i, binaryParameterCoefficient a i •
      binaryNormalMap (binaryParameterGenerator i) := by
  calc
    binaryNormalMap a = binaryNormalMap (∑ i, binaryParameterCoefficient a i •
        binaryParameterGenerator i) := congrArg binaryNormalMap (binaryParameter_expansion a).symm
    _ = _ := by simp only [map_sum, map_smul]

end Atlas.Rudvalis


