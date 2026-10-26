import Atlas.LinearGroups.F4.CentralSevenFormula
import Atlas.LinearGroups.F4.LongRoots

/-! Small integral coefficient certificates identifying the central translations
with the actual positive-grade root groups. No finite-field interpolation is used. -/
namespace Atlas.F4

def centralSevenLongLabel : Fin 6 → Fin 24 := ![0,1,4,5,8,9]

def centralSevenSeedLinearColumn {R : Type*} [CommRing R] (k : Fin 6) (j : Fin 27) :
    Atlas.Albert.Carrier R :=
  ∑ l : Fin 6, if longRootSeedColumn (longRootSeedFor (centralSevenLongLabel k)) l=j then
    ((longRootSeedEntrySign l : R) * (longRootWordSign (longRootWitness (centralSevenLongLabel k))
      (longRootSeedRow (longRootSeedFor (centralSevenLongLabel k)) l) : R)) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (centralSevenLongLabel k))
            (longRootSeedRow (longRootSeedFor (centralSevenLongLabel k)) l))) else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Only six roots, 27 input basis vectors, and their sparse coefficients. -/
theorem centralSeven_integral_coefficients : ∀ (k : Fin 6) (j : Fin 27),
    centralSevenApply (Pi.single k.castSucc (1 : ℤ))
      (longRootWordSign (longRootWitness (centralSevenLongLabel k)) j •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (centralSevenLongLabel k)) j))) =
      longRootWordSign (longRootWitness (centralSevenLongLabel k)) j •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (centralSevenLongLabel k)) j)) +
            centralSevenSeedLinearColumn k j := by
  decide +kernel

variable {R S : Type*} [CommRing R] [CommRing S]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem centralSevenApply_map (φ : R →+* S) (p : Fin 7 → R) (x : Atlas.Albert.Carrier R) :
    centralSevenApply (fun k=>φ (p k)) (Atlas.Albert.map φ x) =
      Atlas.Albert.map φ (centralSevenApply p x) := by
  apply Prod.ext
  · ext i; fin_cases i <;> simp [centralSevenApply,Atlas.Albert.map,Matrix.vecHead,Matrix.vecTail]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [centralSevenApply,Atlas.Albert.map,Matrix.vecHead,Matrix.vecTail]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
/-- Exact degree-one parameter formula for each long direction, over any commutative ring. -/
theorem centralSevenApply_single_long (k : Fin 6) (t : R) (x : Atlas.Albert.Carrier R) :
    centralSevenApply (Pi.single k.castSucc t) x =
      x + t • (centralSevenApply (Pi.single k.castSucc (1 : R)) x - x) := by
  fin_cases k
  all_goals
    apply Prod.ext
    · ext i; fin_cases i <;>
        simp [centralSevenApply,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [centralSevenApply,Pi.single_apply,Matrix.vecHead,Matrix.vecTail] <;> ring

private theorem albertMap_add (φ : R →+* S) (x y : Atlas.Albert.Carrier R) :
    Atlas.Albert.map φ (x+y)=Atlas.Albert.map φ x+Atlas.Albert.map φ y := by
  apply Prod.ext
  · ext i; exact map_add _ _ _
  · ext i j; exact map_add _ _ _

private theorem albertMap_zero (φ : R →+* S) :
    Atlas.Albert.map φ (0 : Atlas.Albert.Carrier R)=0 := by
  apply Prod.ext
  · ext i; exact map_zero _
  · ext i j; exact map_zero _

private theorem albertMap_sum (φ : R →+* S) {ι : Type*} (s : Finset ι)
    (f : ι → Atlas.Albert.Carrier R) :
    Atlas.Albert.map φ (∑ i∈s,f i)=∑ i∈s,Atlas.Albert.map φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [albertMap_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,albertMap_add,ih]

theorem centralSeven_coefficients (k : Fin 6) (j : Fin 27) :
    centralSevenApply (Pi.single k.castSucc (1 : R))
      ((longRootWordSign (longRootWitness (centralSevenLongLabel k)) j : R) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (centralSevenLongLabel k)) j))) =
      (longRootWordSign (longRootWitness (centralSevenLongLabel k)) j : R) •
        Atlas.Albert.basisVector (albertCoordinateOfFin
          (longRootWordDestination (longRootWitness (centralSevenLongLabel k)) j)) +
            centralSevenSeedLinearColumn k j := by
  have hp : (fun l : Fin 7 => (Int.castRingHom R)
      ((Pi.single k.castSucc (1 : ℤ) : Fin 7 → ℤ) l)) =
      Pi.single k.castSucc (1 : R) := by
    ext l
    by_cases h : l=k.castSucc <;> simp [Pi.single_apply,h]
  have h := congrArg (Atlas.Albert.map (Int.castRingHom R)) (centralSeven_integral_coefficients k j)
  rw [←centralSevenApply_map,hp,shortWeyl_map_smul,Atlas.Albert.map_basisVector,
    albertMap_add,shortWeyl_map_smul,Atlas.Albert.map_basisVector] at h
  have hs : Atlas.Albert.map (Int.castRingHom R)
      (centralSevenSeedLinearColumn (R := ℤ) k j)=centralSevenSeedLinearColumn (R := R) k j := by
    unfold centralSevenSeedLinearColumn
    rw [albertMap_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs
    · rw [shortWeyl_map_smul,Atlas.Albert.map_basisVector]
      simp only [map_mul] <;> rfl
    · exact albertMap_zero _
  rw [hs] at h
  exact h

end Atlas.F4
