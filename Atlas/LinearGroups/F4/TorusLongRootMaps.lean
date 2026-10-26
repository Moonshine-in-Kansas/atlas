import Atlas.LinearGroups.F4.LongRoots

/-! Four sparse actual long-root actions used in the simple-coroot words. -/
namespace Atlas.F4
def torusLongLabel : Fin 4 → Fin 24 := ![13,14,21,22]
variable {R : Type*} [CommRing R]

def torusLongApply (k : Fin 4) (t : R) (x : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  ![(![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1 - t*x.2 0 2,x.2 0 2,x.2 0 3,x.2 0 4,x.2 0 5 + t*x.2 0 6,x.2 0 6,x.2 0 7],![x.2 1 0,x.2 1 1 - t*x.2 1 2,x.2 1 2,x.2 1 3,x.2 1 4,x.2 1 5 + t*x.2 1 6,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1 - t*x.2 2 2,x.2 2 2,x.2 2 3,x.2 2 4,x.2 2 5 + t*x.2 2 6,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1,x.2 0 2 + t*x.2 0 1,x.2 0 3,x.2 0 4,x.2 0 5,x.2 0 6 - t*x.2 0 5,x.2 0 7],![x.2 1 0,x.2 1 1,x.2 1 2 + t*x.2 1 1,x.2 1 3,x.2 1 4,x.2 1 5,x.2 1 6 - t*x.2 1 5,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2 + t*x.2 2 1,x.2 2 3,x.2 2 4,x.2 2 5,x.2 2 6 - t*x.2 2 5,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0 + t*x.2 0 1,x.2 0 1,x.2 0 2,x.2 0 3,x.2 0 4,x.2 0 5,x.2 0 6 - t*x.2 0 7,x.2 0 7],![x.2 1 0,x.2 1 1,x.2 1 2 + t*x.2 1 4,x.2 1 3 - t*x.2 1 5,x.2 1 4,x.2 1 5,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2 - t*x.2 2 3,x.2 2 3,x.2 2 4 + t*x.2 2 5,x.2 2 5,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1 - t*x.2 0 0,x.2 0 2,x.2 0 3,x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7 + t*x.2 0 6],![x.2 1 0,x.2 1 1,x.2 1 2,x.2 1 3,x.2 1 4 - t*x.2 1 2,x.2 1 5 + t*x.2 1 3,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3 + t*x.2 2 2,x.2 2 4,x.2 2 5 - t*x.2 2 4,x.2 2 6,x.2 2 7]])] k

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
def torusLongLinear (k : Fin 4) (t : R) : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R where
  toFun := torusLongApply k t
  map_add' x y := by
    fin_cases k
    all_goals
      apply Prod.ext
      · ext i; fin_cases i <;> simp [torusLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
      · ext i j; fin_cases i <;> fin_cases j <;> simp [torusLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
  map_smul' a x := by
    fin_cases k
    all_goals
      apply Prod.ext
      · ext i; fin_cases i <;> simp [torusLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
      · ext i j; fin_cases i <;> fin_cases j <;> simp [torusLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
theorem torusLongApply_parameter (k : Fin 4) (t : R) (x : Atlas.Albert.Carrier R) :
    torusLongApply k t x=x+t • (torusLongApply k 1 x-x) := by
  fin_cases k
  all_goals
    apply Prod.ext
    · ext i; fin_cases i <;> simp [torusLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;> simp [torusLongApply,Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
theorem torusLongApply_map {S : Type*} [CommRing S] (φ : R →+* S)
    (k : Fin 4) (t : R) (x : Atlas.Albert.Carrier R) :
    torusLongApply k (φ t) (Atlas.Albert.map φ x)=Atlas.Albert.map φ (torusLongApply k t x) := by
  fin_cases k
  all_goals
    apply Prod.ext
    · ext i; fin_cases i <;> simp [torusLongApply,Atlas.Albert.map,Matrix.vecHead,Matrix.vecTail]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [torusLongApply,Atlas.Albert.map,Matrix.vecHead,Matrix.vecTail]

def torusLongSeedColumn (k : Fin 4) (j : Fin 27) : Atlas.Albert.Carrier R :=
  ∑ l : Fin 6, if longRootSeedColumn (longRootSeedFor (torusLongLabel k)) l=j then
    ((longRootSeedEntrySign l : R)*(longRootWordSign (longRootWitness (torusLongLabel k))
      (longRootSeedRow (longRootSeedFor (torusLongLabel k)) l) : R)) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (torusLongLabel k))
            (longRootSeedRow (longRootSeedFor (torusLongLabel k)) l))) else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem torusLong_integral_columns : ∀ (k : Fin 4) (j : Fin 27),
    torusLongApply k (1 : ℤ)
      (longRootWordSign (longRootWitness (torusLongLabel k)) j •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (torusLongLabel k)) j))) =
      longRootWordSign (longRootWitness (torusLongLabel k)) j •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (torusLongLabel k)) j)) + torusLongSeedColumn k j := by
  decide +kernel

def albertMapAddHom {S : Type*} [CommRing S] (φ : R →+* S) :
    Atlas.Albert.Carrier R →+ Atlas.Albert.Carrier S where
  toFun := Atlas.Albert.map φ
  map_zero' := by
    apply Prod.ext
    · ext i; exact map_zero _
    · ext i j; exact map_zero _
  map_add' := Atlas.Albert.map_add φ

theorem torusLong_columns (k : Fin 4) (j : Fin 27) :
    torusLongApply k (1 : R)
      ((longRootWordSign (longRootWitness (torusLongLabel k)) j : R) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (torusLongLabel k)) j))) =
      (longRootWordSign (longRootWitness (torusLongLabel k)) j : R) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (torusLongLabel k)) j)) + torusLongSeedColumn k j := by
  have h := congrArg (Atlas.Albert.map (Int.castRingHom R)) (torusLong_integral_columns k j)
  rw [←torusLongApply_map,map_one,shortWeyl_map_smul,Atlas.Albert.map_basisVector,
    Atlas.Albert.map_add,shortWeyl_map_smul,Atlas.Albert.map_basisVector] at h
  have hs : Atlas.Albert.map (Int.castRingHom R) (torusLongSeedColumn (R := ℤ) k j)=
      torusLongSeedColumn (R := R) k j := by
    unfold torusLongSeedColumn
    change (albertMapAddHom (Int.castRingHom R)) (∑ l : Fin 6,_) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs
    · change Atlas.Albert.map (Int.castRingHom R) (_ • _) = _
      rw [shortWeyl_map_smul,Atlas.Albert.map_basisVector]
      simp only [map_mul] <;> rfl
    · exact map_zero (albertMapAddHom (Int.castRingHom R))
  rw [hs] at h
  exact h

end Atlas.F4
