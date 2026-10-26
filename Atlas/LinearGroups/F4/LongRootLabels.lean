import Atlas.LinearGroups.F4.ShortWeylData

/-! Exact integer labels for long-root conjugates. These tables alone assert
no group order, generation or simplicity. -/
namespace Atlas.F4

def longRootLabel (r : Fin 24) : RootData.Root := ⟨r.val,by omega⟩

def longRootStepLabel : Fin 5 → Fin 24 → Fin 24 :=
  ![![2,3,0,1,6,7,4,5,10,11,8,9,12,13,14,15,16,17,18,19,20,21,22,23],
    ![1,0,3,2,4,5,6,7,8,9,10,11,14,15,12,13,18,19,16,17,20,21,22,23],
    ![0,1,2,3,5,4,7,6,8,9,10,11,13,12,15,14,16,17,18,19,22,23,20,21],
    ![0,1,2,3,4,5,6,7,9,8,11,10,12,13,14,15,17,16,19,18,21,20,23,22],
    ![0,20,23,3,4,16,19,7,12,8,11,15,9,13,14,10,17,5,6,18,21,1,2,22]]

def longRootSeedLabel : Fin 3 → Fin 24 := ![0,4,13]

def longRootSeedFor : Fin 24 → Fin 3 :=
  ![0,0,0,0,1,1,1,1,2,2,2,2,2,2,2,2,1,1,1,1,0,0,0,0]

def longRootWitness : Fin 24 → List (Fin 5) :=
  ![[],[1],[0],[0,1],[],[2],[0],[0,2],[1,4,0],[2,4],[1,4],[1,4,3],[2],[],[1,2],[1],[2,4],[0,4,1],[0,4,3],[0,4],[1,4],[0,4,2],[0,4,3],[0,4]]

def longRootWordLabel : List (Fin 5) → Fin 24 → Fin 24
  | [],r => r
  | g::w,r => longRootWordLabel w (longRootStepLabel g r)

theorem longRootWitness_correct : ∀ r : Fin 24,
    longRootWordLabel (longRootWitness r) (longRootSeedLabel (longRootSeedFor r)) = r := by
  decide +kernel

/-- Actual movement of the 27 basis coordinates under the coordinate cycle. -/
def coordinateCycleDestination : Fin 27 → Fin 27 :=
  ![2,0,1,19,20,21,22,23,24,25,26,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]

def longRootStepDestination (g : Fin 5) : Fin 27 → Fin 27 :=
  ![shortWeylDestination 0,shortWeylDestination 1,shortWeylDestination 2,
    shortWeylDestination 3,coordinateCycleDestination] g

def longRootWordDestination : List (Fin 5) → Fin 27 → Fin 27
  | [],j => j
  | g::w,j => longRootWordDestination w (longRootStepDestination g j)

/-- Twice the lattice transformation, avoiding division even for half-coordinate weights. -/
def longRootWeightMatrix (g : Fin 5) (a b : Fin 4) : ℤ :=
  if g.val < 4 then (if a=b then (if a.val=g.val then -2 else 2) else 0)
  else (![![1,1,1,-1],![1,1,-1,1],![1,-1,1,1],![1,-1,-1,-1]] : Fin 4 → Fin 4 → ℤ) a b

def longRootWeightApply (g : Fin 5) (v : RootData.Vector) : RootData.Vector :=
  fun a => ∑ b : Fin 4, longRootWeightMatrix g a b * v b

theorem longRootWeightApply_sub (g : Fin 5) (v w : RootData.Vector) :
    longRootWeightApply g (v-w) = longRootWeightApply g v - longRootWeightApply g w := by
  ext a
  simp [longRootWeightApply,mul_sub,Finset.sum_sub_distrib]

theorem longRootStep_coordinate_weight : ∀ (g : Fin 5) (j : Fin 27) (a : Fin 4),
    2 * Weights.coordinateWeight (albertCoordinateOfFin (longRootStepDestination g j)) a =
      longRootWeightApply g (Weights.coordinateWeight (albertCoordinateOfFin j)) a := by
  decide +kernel

theorem longRootStep_root_weight : ∀ (g : Fin 5) (r : Fin 24) (a : Fin 4),
    2 * RootData.coordinates (longRootLabel (longRootStepLabel g r)) a =
      longRootWeightApply g (RootData.coordinates (longRootLabel r)) a := by
  decide +kernel

theorem longRootStep_weight_difference (g : Fin 5) (r : Fin 24) (j k : Fin 27)
    (h : Weights.coordinateWeight (albertCoordinateOfFin j) -
      Weights.coordinateWeight (albertCoordinateOfFin k) = RootData.coordinates (longRootLabel r)) :
    Weights.coordinateWeight (albertCoordinateOfFin (longRootStepDestination g j)) -
      Weights.coordinateWeight (albertCoordinateOfFin (longRootStepDestination g k)) =
        RootData.coordinates (longRootLabel (longRootStepLabel g r)) := by
  ext a
  have he := congrArg (fun v => longRootWeightApply g v a) h
  rw [longRootWeightApply_sub] at he
  have hj := longRootStep_coordinate_weight g j a
  have hk := longRootStep_coordinate_weight g k a
  have hr := longRootStep_root_weight g r a
  simp only [Pi.sub_apply] at he ⊢
  omega

theorem longRootWord_weight_difference (w : List (Fin 5)) (r : Fin 24) (j k : Fin 27)
    (h : Weights.coordinateWeight (albertCoordinateOfFin j) -
      Weights.coordinateWeight (albertCoordinateOfFin k) = RootData.coordinates (longRootLabel r)) :
    Weights.coordinateWeight (albertCoordinateOfFin (longRootWordDestination w j)) -
      Weights.coordinateWeight (albertCoordinateOfFin (longRootWordDestination w k)) =
        RootData.coordinates (longRootLabel (longRootWordLabel w r)) := by
  induction w generalizing r j k with
  | nil => exact h
  | cons g w ih => exact ih _ _ _ (longRootStep_weight_difference g r j k h)

/-- The six shears in the coefficientwise A, B and E octonion maps. -/
def longRootSeedRow : Fin 3 → Fin 6 → Fin 27 :=
  ![![3,4,11,12,19,20],![3,5,11,13,19,21],![4,8,12,16,20,24]]
def longRootSeedColumn : Fin 3 → Fin 6 → Fin 27 :=
  ![![9,10,17,18,25,26],![8,10,16,18,24,26],![5,9,13,17,21,25]]
def longRootSeedEntrySign : Fin 6 → ℤ := ![-1,1,-1,1,-1,1]

theorem longRootSeed_weight : ∀ (seed : Fin 3) (k : Fin 6),
    Weights.coordinateWeight (albertCoordinateOfFin (longRootSeedRow seed k)) -
      Weights.coordinateWeight (albertCoordinateOfFin (longRootSeedColumn seed k)) =
        RootData.coordinates (longRootLabel (longRootSeedLabel seed)) := by
  decide +kernel

/-- Every transformed shear has exactly the advertised root weight. -/
theorem longRootWitness_shear_weight (r : Fin 24) (k : Fin 6) :
    Weights.coordinateWeight (albertCoordinateOfFin (longRootWordDestination (longRootWitness r)
      (longRootSeedRow (longRootSeedFor r) k))) -
      Weights.coordinateWeight (albertCoordinateOfFin (longRootWordDestination (longRootWitness r)
        (longRootSeedColumn (longRootSeedFor r) k))) = RootData.coordinates (longRootLabel r) := by
  simpa only [longRootWitness_correct] using
    longRootWord_weight_difference (longRootWitness r) _ _ _ (longRootSeed_weight (longRootSeedFor r) k)

end Atlas.F4
