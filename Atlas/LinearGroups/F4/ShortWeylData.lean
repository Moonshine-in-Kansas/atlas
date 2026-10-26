import Atlas.LinearGroups.F4.ShortRoots
import Atlas.LinearGroups.F4.Weights

/-! Explicit signed Albert basis permutations for the short-root Weyl lifts.
The tables are checked against the actual integral root formulas by the kernel. -/
namespace Atlas.F4

def albertCoordinateOfFin (j : Fin 27) : Atlas.Albert.Coordinate :=
  if h : j.val < 3 then .inl ⟨j.val,h⟩
  else .inr (⟨(j.val-3)/8,by omega⟩, ⟨(j.val-3)%8,by omega⟩)

def albertCoordinateToFin : Atlas.Albert.Coordinate → Fin 27
  | .inl i => ⟨i.val,by omega⟩
  | .inr (i,j) => ⟨3+8*i.val+j.val,by omega⟩

def albertCoordinateFinEquiv : Atlas.Albert.Coordinate ≃ Fin 27 where
  toFun := albertCoordinateToFin
  invFun := albertCoordinateOfFin
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def shortWeylAxis (i : Fin 8) : Fin 4 := ⟨min i.val (7-i.val),by omega⟩

def shortWeylDestination (i : Fin 8) : Fin 27 → Fin 27 :=
  (![![1,0,2,14,16,17,18,11,12,13,15,7,8,9,3,10,4,5,6,26,20,21,22,23,24,25,19],
     ![1,0,2,13,15,11,12,17,18,14,16,5,6,3,9,4,10,7,8,19,25,21,22,23,24,20,26],
     ![1,0,2,12,11,15,13,16,14,18,17,4,3,6,8,5,7,10,9,19,20,24,22,23,21,25,26],
     ![1,0,2,11,12,13,15,14,16,17,18,3,4,5,7,6,8,9,10,19,20,21,23,22,24,25,26]] :
    Fin 4 → Fin 27 → Fin 27) (shortWeylAxis i)

def shortWeylSign (i : Fin 8) : Fin 27 → ℤ :=
  (![![1,1,1,1,-1,1,1,1,1,-1,1,-1,-1,1,-1,-1,1,-1,-1,-1,1,1,1,1,1,1,-1],
     ![1,1,1,1,1,-1,1,1,-1,1,1,1,-1,-1,-1,-1,-1,-1,1,1,-1,1,1,1,1,-1,1],
     ![1,1,1,-1,1,1,1,1,1,1,-1,-1,1,-1,-1,-1,-1,1,-1,1,1,-1,1,1,-1,1,1],
     ![1,1,1,1,1,1,-1,-1,1,1,1,-1,-1,-1,1,1,-1,-1,-1,1,1,1,-1,-1,1,1,1]] :
    Fin 4 → Fin 27 → ℤ) (shortWeylAxis i)

theorem shortWeylDestination_involutive : ∀ i : Fin 8,
    Function.Involutive (shortWeylDestination i) := by
  unfold Function.Involutive
  decide +kernel

theorem shortWeylSign_sq : ∀ (i : Fin 8) (j : Fin 27), shortWeylSign i j ^ 2 = 1 := by
  decide +kernel

def shortWeylPermutation (i : Fin 8) : Equiv.Perm (Fin 27) :=
  Function.Involutive.toPerm (shortWeylDestination i) (shortWeylDestination_involutive i)

def shortWeylApply {R : Type*} [CommRing R] (i : Fin 8)
    (x : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  Atlas.Albert.shortRootLinear i 1
    (Atlas.Albert.shortRootLinear (7-i) 1 (Atlas.Albert.shortRootLinear i 1 x))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
/-- Complete integral basis check of the proposed signed permutations. -/
theorem shortWeyl_integral_basis : ∀ (i : Fin 8) (j : Fin 27),
    shortWeylApply i (Atlas.Albert.basisVector (albertCoordinateOfFin j) : Atlas.Albert.Carrier ℤ) =
      shortWeylSign i j • Atlas.Albert.basisVector
        (albertCoordinateOfFin (shortWeylDestination i j)) := by decide +kernel

/-- These signed permutations act on weights by the corresponding axial reflection. -/
theorem shortWeyl_weight : ∀ (i : Fin 8) (j : Fin 27) (k : Fin 4),
    Weights.coordinateWeight (albertCoordinateOfFin (shortWeylDestination i j)) k =
      if k = shortWeylAxis i then -Weights.coordinateWeight (albertCoordinateOfFin j) k
      else Weights.coordinateWeight (albertCoordinateOfFin j) k := by decide +kernel

end Atlas.F4
