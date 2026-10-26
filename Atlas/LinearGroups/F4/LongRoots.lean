import Atlas.LinearGroups.F4.LongRootLabels
import Atlas.LinearGroups.F4.LongRootSeedsDerived
import Atlas.LinearGroups.F4.ShortWeyl

/-! Twenty-four explicit long-root groups in the full split Albert model.
The labels are verified from the six actual shears, not from group recognition.
No generation, fullness or simplicity assertion is made here. -/
noncomputable section
namespace Atlas.F4

private theorem coordinateCycle_integral_basis : ∀ j : Fin 27,
    Atlas.Albert.coordinateCycle (Atlas.Albert.basisVector (albertCoordinateOfFin j) :
      Atlas.Albert.Carrier ℤ) =
        Atlas.Albert.basisVector (albertCoordinateOfFin (coordinateCycleDestination j)) := by
  decide +kernel

theorem coordinateCycle_basis {R : Type*} [CommRing R] (j : Fin 27) :
    Atlas.Albert.coordinateCycle (Atlas.Albert.basisVector (albertCoordinateOfFin j) :
      Atlas.Albert.Carrier R) =
        Atlas.Albert.basisVector (albertCoordinateOfFin (coordinateCycleDestination j)) := by
  have h := congrArg (Atlas.Albert.map (Int.castRingHom R)) (coordinateCycle_integral_basis j)
  rw [←Atlas.Albert.coordinateCycle_map,Atlas.Albert.map_basisVector,
    Atlas.Albert.map_basisVector] at h
  exact h

variable {F : Type*} [Field F]

def longRootStepElement (g : Fin 5) : Model F :=
  ![shortWeylFirstPair 0,shortWeylFirstPair 1,shortWeylFirstPair 2,
    shortWeylFirstPair 3,coordinateCycle] g

def longRootStepSign (g : Fin 5) (j : Fin 27) : ℤ :=
  ![shortWeylSign 0,shortWeylSign 1,shortWeylSign 2,shortWeylSign 3,fun _=>1] g j

theorem longRootStepElement_basis (g : Fin 5) (j : Fin 27) :
    (longRootStepElement (F := F) g).val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) =
      (longRootStepSign g j : F) • Atlas.Albert.basisVector
        (albertCoordinateOfFin (longRootStepDestination g j)) := by
  fin_cases g
  · exact shortWeylFirstPair_basis 0 j
  · exact shortWeylFirstPair_basis 1 j
  · exact shortWeylFirstPair_basis 2 j
  · exact shortWeylFirstPair_basis 3 j
  · simpa [longRootStepElement,longRootStepSign,longRootStepDestination,coordinateCycle_apply]
      using coordinateCycle_basis (R := F) j

/-- Chronological words: the first letter acts first. -/
def longRootWordElement : List (Fin 5) → Model F
  | [] => 1
  | g::w => longRootWordElement w * longRootStepElement g

def longRootWordSign : List (Fin 5) → Fin 27 → ℤ
  | [],_ => 1
  | g::w,j => longRootStepSign g j * longRootWordSign w (longRootStepDestination g j)

theorem longRootWordElement_basis (w : List (Fin 5)) (j : Fin 27) :
    (longRootWordElement (F := F) w).val (Atlas.Albert.basisVector (albertCoordinateOfFin j)) =
      (longRootWordSign w j : F) • Atlas.Albert.basisVector
        (albertCoordinateOfFin (longRootWordDestination w j)) := by
  induction w generalizing j with
  | nil => simp [longRootWordElement,longRootWordSign,longRootWordDestination]
  | cons g w ih =>
    change (longRootWordElement w).val
      ((longRootStepElement g).val (Atlas.Albert.basisVector (albertCoordinateOfFin j))) = _
    rw [longRootStepElement_basis,map_smul,ih,smul_smul]
    simp only [longRootWordSign,longRootWordDestination,Int.cast_mul]

theorem albertCoordinateEquiv_apply (x : Atlas.Albert.Carrier F) (c : Atlas.Albert.Coordinate) :
    Atlas.Albert.coordinateEquiv x c = Sum.elim x.1 (fun p => x.2 p.1 p.2) c := rfl

theorem longRootSeeds_apply (seed : Fin 3) (t : F) (x : Atlas.Albert.Carrier F) :
    (longRootSeeds seed t).val x =
      (x.1,fun j => (![Atlas.G2.Explicit.rootAApply t,Atlas.G2.Explicit.rootBApply t,
        Atlas.G2.Explicit.rootEApply t] : Fin 3 → Atlas.SplitOctonion.Carrier F →
          Atlas.SplitOctonion.Carrier F) seed (x.2 j)) := by
  fin_cases seed <;> rfl

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
/-- Actual six-entry formula for the three embedded octonion seed groups. -/
theorem longRootSeeds_shears (seed : Fin 3) (t : F) (x : Atlas.Albert.Carrier F) :
    (longRootSeeds seed t).val x = x + t • ∑ k : Fin 6,
      ((longRootSeedEntrySign k : F) *
        Atlas.Albert.coordinateEquiv x (albertCoordinateOfFin (longRootSeedColumn seed k))) •
          Atlas.Albert.basisVector (albertCoordinateOfFin (longRootSeedRow seed k)) := by
  rw [longRootSeeds_apply]
  fin_cases seed
  all_goals
    apply Prod.ext
    · funext j
      fin_cases j <;>
        simp [albertCoordinateEquiv_apply,Atlas.Albert.basisVector,
          longRootSeedEntrySign,longRootSeedColumn,longRootSeedRow,albertCoordinateOfFin,
          Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail]
    · funext j l
      fin_cases j <;> fin_cases l <;>
        simp [albertCoordinateEquiv_apply,Atlas.Albert.basisVector,
          Atlas.G2.Explicit.rootAApply,Atlas.G2.Explicit.rootBApply,Atlas.G2.Explicit.rootEApply,
          longRootSeedEntrySign,longRootSeedColumn,longRootSeedRow,albertCoordinateOfFin,
          Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring

/-- Every label is an actual conjugate of one of the A/B/E long-root seed groups. -/
def longRoot (r : Fin 24) (t : F) : Model F :=
  longRootWordElement (longRootWitness r) * longRootSeeds (longRootSeedFor r) t *
    (longRootWordElement (longRootWitness r))⁻¹

theorem longRoot_add (r : Fin 24) (s t : F) :
    longRoot r s * longRoot r t = longRoot r (s+t) := by
  unfold longRoot
  rw [←longRootSeeds_add]
  group

theorem longRoot_injective (r : Fin 24) : Function.Injective (longRoot (F := F) r) := by
  intro s t h
  exact longRootSeeds_injective _ (mul_left_cancel (mul_right_cancel h))

theorem longRoot_mem_commutator (r : Fin 24) (t : F) :
    longRoot r t ∈ commutator (Model F) :=
  (inferInstance : (commutator (Model F)).Normal).conj_mem _
    (longRootSeeds_mem_commutator _ t) _

/-- The six seed shears transported through their actual signed basis permutation. -/
theorem longRoot_conjugated_apply (r : Fin 24) (t : F) (x : Atlas.Albert.Carrier F) :
    (longRoot r t).val ((longRootWordElement (longRootWitness r)).val x) =
      (longRootWordElement (longRootWitness r)).val x + t • ∑ k : Fin 6,
        ((longRootSeedEntrySign k : F) * Atlas.Albert.coordinateEquiv x
          (albertCoordinateOfFin (longRootSeedColumn (longRootSeedFor r) k))) •
            ((longRootWordSign (longRootWitness r)
              (longRootSeedRow (longRootSeedFor r) k) : F) • Atlas.Albert.basisVector
              (albertCoordinateOfFin (longRootWordDestination (longRootWitness r)
                (longRootSeedRow (longRootSeedFor r) k)))) := by
  change (longRootWordElement (longRootWitness r)).val
    ((longRootSeeds (longRootSeedFor r) t).val
      ((longRootWordElement (longRootWitness r)).val.symm
        ((longRootWordElement (longRootWitness r)).val x))) = _
  rw [LinearEquiv.symm_apply_apply,longRootSeeds_shears,map_add,map_smul,map_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul,longRootWordElement_basis]

end Atlas.F4
