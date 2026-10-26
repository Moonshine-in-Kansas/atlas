import Atlas.LinearGroups.F4.LongRoots

/-! The twelve sparse actual long-root actions in the B₃ Levi subsystem. -/
namespace Atlas.F4
def leviLongLabel : Fin 12 → Fin 24 := ![12,13,14,15,16,17,18,19,20,21,22,23]
variable {R : Type*} [CommRing R]

def leviLongApply (k : Fin 12) (t : R) (x : Atlas.Albert.Carrier R) : Atlas.Albert.Carrier R :=
  ![(![x.1 0,x.1 1,x.1 2],![![x.2 0 0 + t*x.2 0 3,x.2 0 1,x.2 0 2,x.2 0 3,x.2 0 4 - t*x.2 0 7,x.2 0 5,x.2 0 6,x.2 0 7],![x.2 1 0 - t*x.2 1 4,x.2 1 1,x.2 1 2,x.2 1 3 + t*x.2 1 7,x.2 1 4,x.2 1 5,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1 + t*x.2 2 5,x.2 2 2 - t*x.2 2 6,x.2 2 3,x.2 2 4,x.2 2 5,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1 - t*x.2 0 2,x.2 0 2,x.2 0 3,x.2 0 4,x.2 0 5 + t*x.2 0 6,x.2 0 6,x.2 0 7],![x.2 1 0,x.2 1 1 - t*x.2 1 2,x.2 1 2,x.2 1 3,x.2 1 4,x.2 1 5 + t*x.2 1 6,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1 - t*x.2 2 2,x.2 2 2,x.2 2 3,x.2 2 4,x.2 2 5 + t*x.2 2 6,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1,x.2 0 2 + t*x.2 0 1,x.2 0 3,x.2 0 4,x.2 0 5,x.2 0 6 - t*x.2 0 5,x.2 0 7],![x.2 1 0,x.2 1 1,x.2 1 2 + t*x.2 1 1,x.2 1 3,x.2 1 4,x.2 1 5,x.2 1 6 - t*x.2 1 5,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2 + t*x.2 2 1,x.2 2 3,x.2 2 4,x.2 2 5,x.2 2 6 - t*x.2 2 5,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1,x.2 0 2,x.2 0 3 - t*x.2 0 0,x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7 + t*x.2 0 4],![x.2 1 0,x.2 1 1,x.2 1 2,x.2 1 3,x.2 1 4 + t*x.2 1 0,x.2 1 5,x.2 1 6,x.2 1 7 - t*x.2 1 3],![x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3,x.2 2 4,x.2 2 5 - t*x.2 2 1,x.2 2 6 + t*x.2 2 2,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1 + t*x.2 0 3,x.2 0 2,x.2 0 3,x.2 0 4 - t*x.2 0 6,x.2 0 5,x.2 0 6,x.2 0 7],![x.2 1 0 + t*x.2 1 2,x.2 1 1,x.2 1 2,x.2 1 3,x.2 1 4,x.2 1 5 - t*x.2 1 7,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1 - t*x.2 2 4,x.2 2 2,x.2 2 3 + t*x.2 2 6,x.2 2 4,x.2 2 5,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0 + t*x.2 0 2,x.2 0 1,x.2 0 2,x.2 0 3,x.2 0 4,x.2 0 5 - t*x.2 0 7,x.2 0 6,x.2 0 7],![x.2 1 0,x.2 1 1 - t*x.2 1 4,x.2 1 2,x.2 1 3 + t*x.2 1 6,x.2 1 4,x.2 1 5,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1 + t*x.2 2 3,x.2 2 2,x.2 2 3,x.2 2 4 - t*x.2 2 6,x.2 2 5,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1,x.2 0 2 - t*x.2 0 0,x.2 0 3,x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7 + t*x.2 0 5],![x.2 1 0,x.2 1 1,x.2 1 2,x.2 1 3,x.2 1 4 + t*x.2 1 1,x.2 1 5,x.2 1 6 - t*x.2 1 3,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3 - t*x.2 2 1,x.2 2 4,x.2 2 5,x.2 2 6 + t*x.2 2 4,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1,x.2 0 2,x.2 0 3 - t*x.2 0 1,x.2 0 4,x.2 0 5,x.2 0 6 + t*x.2 0 4,x.2 0 7],![x.2 1 0,x.2 1 1,x.2 1 2 - t*x.2 1 0,x.2 1 3,x.2 1 4,x.2 1 5,x.2 1 6,x.2 1 7 + t*x.2 1 5],![x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3,x.2 2 4 + t*x.2 2 1,x.2 2 5,x.2 2 6 - t*x.2 2 3,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1,x.2 0 2 - t*x.2 0 3,x.2 0 3,x.2 0 4 + t*x.2 0 5,x.2 0 5,x.2 0 6,x.2 0 7],![x.2 1 0 + t*x.2 1 1,x.2 1 1,x.2 1 2,x.2 1 3,x.2 1 4,x.2 1 5,x.2 1 6 - t*x.2 1 7,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2 + t*x.2 2 4,x.2 2 3 - t*x.2 2 5,x.2 2 4,x.2 2 5,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0 + t*x.2 0 1,x.2 0 1,x.2 0 2,x.2 0 3,x.2 0 4,x.2 0 5,x.2 0 6 - t*x.2 0 7,x.2 0 7],![x.2 1 0,x.2 1 1,x.2 1 2 + t*x.2 1 4,x.2 1 3 - t*x.2 1 5,x.2 1 4,x.2 1 5,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2 - t*x.2 2 3,x.2 2 3,x.2 2 4 + t*x.2 2 5,x.2 2 5,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1 - t*x.2 0 0,x.2 0 2,x.2 0 3,x.2 0 4,x.2 0 5,x.2 0 6,x.2 0 7 + t*x.2 0 6],![x.2 1 0,x.2 1 1,x.2 1 2,x.2 1 3,x.2 1 4 - t*x.2 1 2,x.2 1 5 + t*x.2 1 3,x.2 1 6,x.2 1 7],![x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3 + t*x.2 2 2,x.2 2 4,x.2 2 5 - t*x.2 2 4,x.2 2 6,x.2 2 7]]),
    (![x.1 0,x.1 1,x.1 2],![![x.2 0 0,x.2 0 1,x.2 0 2,x.2 0 3 + t*x.2 0 2,x.2 0 4,x.2 0 5 - t*x.2 0 4,x.2 0 6,x.2 0 7],![x.2 1 0,x.2 1 1 - t*x.2 1 0,x.2 1 2,x.2 1 3,x.2 1 4,x.2 1 5,x.2 1 6,x.2 1 7 + t*x.2 1 6],![x.2 2 0,x.2 2 1,x.2 2 2,x.2 2 3,x.2 2 4 - t*x.2 2 2,x.2 2 5 + t*x.2 2 3,x.2 2 6,x.2 2 7]])] k

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
def leviLongLinear (k : Fin 12) (t : R) : Atlas.Albert.Carrier R →ₗ[R] Atlas.Albert.Carrier R where
  toFun := leviLongApply k t
  map_add' x y := by
    fin_cases k
    all_goals
      simp only [leviLongApply,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Matrix.cons_val_zero',Matrix.cons_val_succ']
      apply Prod.ext
      · ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail] <;> ring
      · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.vecHead,Matrix.vecTail] <;> ring
  map_smul' a x := by
    fin_cases k
    all_goals
      simp only [leviLongApply,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Matrix.cons_val_zero',Matrix.cons_val_succ']
      apply Prod.ext
      · ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail] <;> ring
      · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
theorem leviLongApply_parameter (k : Fin 12) (t : R) (x : Atlas.Albert.Carrier R) :
    leviLongApply k t x=x+t • (leviLongApply k 1 x-x) := by
  fin_cases k
  all_goals
    simp only [leviLongApply,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.cons_val_zero',Matrix.cons_val_succ']
    apply Prod.ext
    · ext i; fin_cases i <;> simp [Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.vecHead,Matrix.vecTail] <;> ring

set_option maxHeartbeats 1600000 in
theorem leviLongApply_map {S : Type*} [CommRing S] (φ : R →+* S)
    (k : Fin 12) (t : R) (x : Atlas.Albert.Carrier R) :
    leviLongApply k (φ t) (Atlas.Albert.map φ x)=Atlas.Albert.map φ (leviLongApply k t x) := by
  fin_cases k
  all_goals
    simp only [leviLongApply,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Matrix.cons_val_zero',Matrix.cons_val_succ']
    apply Prod.ext
    · ext i; fin_cases i <;> simp [Atlas.Albert.map,Matrix.vecHead,Matrix.vecTail]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [Atlas.Albert.map,Matrix.vecHead,Matrix.vecTail]

def leviLongSeedColumn (k : Fin 12) (j : Fin 27) : Atlas.Albert.Carrier R :=
  ∑ l : Fin 6, if longRootSeedColumn (longRootSeedFor (leviLongLabel k)) l=j then
    ((longRootSeedEntrySign l : R)*(longRootWordSign (longRootWitness (leviLongLabel k))
      (longRootSeedRow (longRootSeedFor (leviLongLabel k)) l) : R)) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (leviLongLabel k))
            (longRootSeedRow (longRootSeedFor (leviLongLabel k)) l))) else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem leviLong_integral_columns : ∀ (k : Fin 12) (j : Fin 27),
    leviLongApply k (1 : ℤ)
      (longRootWordSign (longRootWitness (leviLongLabel k)) j •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (leviLongLabel k)) j))) =
      longRootWordSign (longRootWitness (leviLongLabel k)) j •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (leviLongLabel k)) j)) + leviLongSeedColumn k j := by
  decide +kernel

def leviMapAddHom {S : Type*} [CommRing S] (φ : R →+* S) :
    Atlas.Albert.Carrier R →+ Atlas.Albert.Carrier S where
  toFun := Atlas.Albert.map φ
  map_zero' := by
    apply Prod.ext
    · ext i; exact map_zero _
    · ext i j; exact map_zero _
  map_add' := Atlas.Albert.map_add φ

theorem leviLong_columns (k : Fin 12) (j : Fin 27) :
    leviLongApply k (1 : R)
      ((longRootWordSign (longRootWitness (leviLongLabel k)) j : R) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (leviLongLabel k)) j))) =
      (longRootWordSign (longRootWitness (leviLongLabel k)) j : R) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (leviLongLabel k)) j)) + leviLongSeedColumn k j := by
  have h := congrArg (Atlas.Albert.map (Int.castRingHom R)) (leviLong_integral_columns k j)
  rw [←leviLongApply_map,map_one,shortWeyl_map_smul,Atlas.Albert.map_basisVector,
    Atlas.Albert.map_add,shortWeyl_map_smul,Atlas.Albert.map_basisVector] at h
  have hs : Atlas.Albert.map (Int.castRingHom R) (leviLongSeedColumn (R := ℤ) k j)=
      leviLongSeedColumn (R := R) k j := by
    unfold leviLongSeedColumn
    change (leviMapAddHom (Int.castRingHom R)) (∑ l : Fin 6,_) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs
    · change Atlas.Albert.map (Int.castRingHom R) (_ • _) = _
      rw [shortWeyl_map_smul,Atlas.Albert.map_basisVector]
      simp only [map_mul] <;> rfl
    · exact map_zero (leviMapAddHom (Int.castRingHom R))
  rw [hs] at h
  exact h

end Atlas.F4
