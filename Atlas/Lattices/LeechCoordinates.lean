import Atlas.Lattices.LeechMinimum
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def coordinateVector (a : Omega) (r : ℤ) : IntegerCoordinates := Pi.single a r

theorem integerDot_coordinateVector (x : IntegerCoordinates) (a : Omega) (r : ℤ) :
    integerDot x (coordinateVector a r) = x a * r := by
  simp [integerDot,coordinateVector,Pi.single_apply,mul_ite]

theorem coordinate_eight_mem_even (a : Omega) : coordinateVector a 8 ∈ evenGolayLattice := by
  apply (mem_evenGolayLattice _).mpr
  refine ⟨coordinateVector a 4,?_,?_,?_⟩
  · have h : integerReduction (coordinateVector a 4) = 0 := by
      ext i
      change ((coordinateVector a 4 i : ℤ) : Bit) = 0
      by_cases hi : i = a <;> simp [coordinateVector,Pi.single_apply,hi]
    rw [h]; exact golay.zero_mem
  · simp [coordinateVector]
  · intro i
    by_cases hi : i = a <;> simp [coordinateVector,Pi.single_apply,hi]

theorem coordinate_pair_mem_even (a b : Omega) :
    coordinateVector a 4 + coordinateVector b 4 ∈ evenGolayLattice := by
  apply (mem_evenGolayLattice _).mpr
  refine ⟨coordinateVector a 2 + coordinateVector b 2,?_,?_,?_⟩
  · have h (j : Omega) : integerReduction (coordinateVector j 2) = 0 := by
      ext i
      change ((coordinateVector j 2 i : ℤ) : Bit) = 0
      by_cases hi : i = j <;> simp [coordinateVector,Pi.single_apply,hi]
    rw [map_add,h,h,add_zero]; exact golay.zero_mem
  · simp [coordinateVector,Finset.sum_add_distrib]
  · intro i
    simp only [Pi.add_apply,coordinateVector,Pi.single_apply]
    split_ifs <;> ring

theorem coordinate_eight_mem (a : Omega) : coordinateVector a 8 ∈ leech :=
  Or.inl (coordinate_eight_mem_even a)

theorem coordinate_pair_mem (a b : Omega) :
    coordinateVector a 4 + coordinateVector b 4 ∈ leech :=
  Or.inl (coordinate_pair_mem_even a b)

def rationalLeech : Submodule ℤ RationalCoordinates := leech.map rationalEmbedding

def leechDual : Submodule ℤ RationalCoordinates := rationalForm.dualSubmodule rationalLeech

theorem rationalLeech_le_dual : rationalLeech ≤ leechDual := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  obtain ⟨k,hk⟩ := leech_pairing_integral ⟨x,hx⟩ ⟨y,hy⟩
  exact Submodule.mem_one.mpr ⟨k,hk.symm⟩

end Atlas.Lattices
