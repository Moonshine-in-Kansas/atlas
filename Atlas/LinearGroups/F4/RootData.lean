import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! Integral doubled labels for F₄. These coordinates are combinatorial integers,
not field elements; no inverse of 2 in a coefficient field is used. This file
contains no group transformations and asserts no commutator identities. -/
namespace Atlas.F4.RootData
open scoped BigOperators

abbrev Root := Fin 48
abbrev Vector := Fin 4 → ℤ

/-- Long labels first, then axial and half-coordinate short labels. -/
def coordinates : Root → Vector :=
  ![![2,2,0,0],
    ![2,-2,0,0],
    ![-2,2,0,0],
    ![-2,-2,0,0],
    ![2,0,2,0],
    ![2,0,-2,0],
    ![-2,0,2,0],
    ![-2,0,-2,0],
    ![2,0,0,2],
    ![2,0,0,-2],
    ![-2,0,0,2],
    ![-2,0,0,-2],
    ![0,2,2,0],
    ![0,2,-2,0],
    ![0,-2,2,0],
    ![0,-2,-2,0],
    ![0,2,0,2],
    ![0,2,0,-2],
    ![0,-2,0,2],
    ![0,-2,0,-2],
    ![0,0,2,2],
    ![0,0,2,-2],
    ![0,0,-2,2],
    ![0,0,-2,-2],
    ![2,0,0,0],
    ![-2,0,0,0],
    ![0,2,0,0],
    ![0,-2,0,0],
    ![0,0,2,0],
    ![0,0,-2,0],
    ![0,0,0,2],
    ![0,0,0,-2],
    ![1,1,1,1],
    ![1,1,1,-1],
    ![1,1,-1,1],
    ![1,1,-1,-1],
    ![1,-1,1,1],
    ![1,-1,1,-1],
    ![1,-1,-1,1],
    ![1,-1,-1,-1],
    ![-1,1,1,1],
    ![-1,1,1,-1],
    ![-1,1,-1,1],
    ![-1,1,-1,-1],
    ![-1,-1,1,1],
    ![-1,-1,1,-1],
    ![-1,-1,-1,1],
    ![-1,-1,-1,-1]]

def normSquared (v : Vector) : ℤ := ∑i,v i^2

def IsLong (r : Root) : Prop := r.val<24
instance (r : Root) : Decidable (IsLong r) := inferInstanceAs (Decidable (r.val<24))
def IsShort (r : Root) : Prop := ¬IsLong r
instance (r : Root) : Decidable (IsShort r) := inferInstanceAs (Decidable (¬IsLong r))

theorem coordinates_injective : Function.Injective coordinates := by decide +kernel

theorem root_count : Fintype.card Root=48 := rfl

theorem long_count : Fintype.card {r : Root // IsLong r}=24 := by decide +kernel

theorem short_count : Fintype.card {r : Root // IsShort r}=24 := by decide +kernel

theorem norm_coordinates : ∀r : Root,normSquared (coordinates r)=if IsLong r then 8 else 4 := by
  decide +kernel

/-- Simple-root coefficients with respect to the specified α₁,α₂,α₃,α₄. -/
def simpleCoefficients (r : Root) : Vector :=
  let v := coordinates r
  ![(v 1+v 0)/2,(v 2+v 1+2*v 0)/2,(v 3+v 2+v 1+3*v 0)/2,v 0]

def simpleRoot : Fin 4 → Root := ![13,21,30,39]

theorem simpleRoot_coordinates : ∀i : Fin 4,coordinates (simpleRoot i)=
    (![![0,2,-2,0],![0,0,2,-2],![0,0,0,2],![1,-1,-1,-1]] : Fin 4 → Vector) i := by
  decide +kernel

theorem simpleCoefficients_reconstruct : ∀r : Root,
    coordinates r=∑i,simpleCoefficients r i • coordinates (simpleRoot i) := by
  decide +kernel

def IsPositive (r : Root) : Prop := ∀i,0≤simpleCoefficients r i
instance (r : Root) : Decidable (IsPositive r) := inferInstanceAs (Decidable (∀i,0≤simpleCoefficients r i))
def height (r : Root) : ℤ := ∑i,simpleCoefficients r i

def InB3 (r : Root) : Prop := coordinates r 0=0
instance (r : Root) : Decidable (InB3 r) := inferInstanceAs (Decidable (coordinates r 0=0))

theorem b3_iff_fourth_coefficient_zero : ∀r : Root,InB3 r ↔ simpleCoefficients r 3=0 := by
  decide +kernel

theorem b3_count : Fintype.card {r : Root // InB3 r}=18 := by decide +kernel

theorem positive_count : Fintype.card {r : Root // IsPositive r}=24 := by decide +kernel

theorem b3_positive_count : Fintype.card {r : Root // InB3 r ∧ IsPositive r}=9 := by decide +kernel

theorem outside_b3_positive_count : Fintype.card {r : Root // ¬InB3 r ∧ IsPositive r}=15 := by decide +kernel

/-- Reflections in the four marked simple roots, as explicit finite permutations. -/
def simpleReflectionIndex : Fin 4 → Root → Root :=
  ![![4,5,6,7,0,1,2,3,8,9,10,11,12,14,13,15,20,21,22,23,16,17,18,19,24,25,28,29,26,27,30,31,32,33,36,37,34,35,38,39,40,41,44,45,42,43,46,47],
    ![0,1,2,3,8,9,10,11,4,5,6,7,16,17,18,19,12,13,14,15,20,22,21,23,24,25,26,27,30,31,28,29,32,34,33,35,36,38,37,39,40,42,41,43,44,46,45,47],
    ![0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15,17,16,19,18,21,20,23,22,24,25,26,27,28,29,31,30,33,32,35,34,37,36,39,38,41,40,43,42,45,44,47,46],
    ![0,20,23,3,4,16,19,7,8,12,15,11,9,13,14,10,5,17,18,6,1,21,22,2,32,47,35,44,37,42,38,41,24,33,34,26,36,28,30,40,39,31,29,43,27,45,46,25]]

theorem simpleReflectionIndex_involutive : ∀i : Fin 4,∀r : Root,
    simpleReflectionIndex i (simpleReflectionIndex i r)=r := by decide +kernel

def simpleReflection (i : Fin 4) : Equiv.Perm Root where
  toFun := simpleReflectionIndex i
  invFun := simpleReflectionIndex i
  left_inv := simpleReflectionIndex_involutive i
  right_inv := simpleReflectionIndex_involutive i

theorem simpleReflection_formula : ∀i : Fin 4,∀r : Root,
    coordinates (simpleReflection i r)=coordinates r-
      ((2*∑j,coordinates r j*coordinates (simpleRoot i) j)/normSquared (coordinates (simpleRoot i))) •
        coordinates (simpleRoot i) := by decide +kernel

/-- Label witnesses only. Their associated actual transformations require separate proofs. -/
def a2Witness : Root → Root × Root :=
  ![(4,13),(4,15),(6,13),(6,15),(0,14),(0,15),(2,14),(2,15),(0,18),(0,19),(2,18),(2,19),(0,6),(0,7),(1,6),(1,7),(0,10),(0,11),(1,10),(1,11),(4,10),(4,11),(5,10),(5,11),(32,39),(40,47),(32,43),(36,47),(32,45),(34,47),(32,46),(33,47),(24,40),(24,41),(24,42),(24,43),(24,44),(24,45),(24,46),(24,47),(25,32),(25,33),(25,34),(25,35),(25,36),(25,37),(25,38),(25,39)]

theorem a2Witness_sum : ∀r : Root,coordinates r=
    coordinates (a2Witness r).1+coordinates (a2Witness r).2 := by decide +kernel

theorem a2Witness_same_length : ∀r : Root,
    normSquared (coordinates (a2Witness r).1)=normSquared (coordinates r) ∧
    normSquared (coordinates (a2Witness r).2)=normSquared (coordinates r) := by decide +kernel

theorem a2Witness_difference_not_root : ∀r s : Root,
    coordinates s≠coordinates (a2Witness r).1-coordinates (a2Witness r).2 := by decide +kernel

end Atlas.F4.RootData
