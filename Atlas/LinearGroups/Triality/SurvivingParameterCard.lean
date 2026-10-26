import Atlas.LinearGroups.Triality.BruhatIntersectionCoordinates

/-! Counting the unrestricted field coordinates of each Borel intersection. -/
noncomputable section
namespace Atlas.Triality

/-- A coordinate is free if the indicated root survives, and zero otherwise. -/
def AllowedCoordinate (A : Type*) [Zero A] (b : Bool) := {x : A // b=false → x=0}

def allowedCoordinateTrue (A : Type*) [Zero A] : AllowedCoordinate A true ≃ A where
  toFun := Subtype.val
  invFun := fun x => ⟨x,by simp⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

def allowedCoordinateFalse (A : Type*) [Zero A] : AllowedCoordinate A false ≃ PUnit.{1} where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => ⟨0,by simp⟩
  left_inv := by intro x; apply Subtype.ext; exact (x.property rfl).symm
  right_inv := by intro x; cases x; rfl

theorem card_allowedCoordinate (A : Type*) [Zero A] (b : Bool) :
    Nat.card (AllowedCoordinate A b) = if b then Nat.card A else 1 := by
  cases b
  · simpa using Nat.card_congr (allowedCoordinateFalse A)
  · exact Nat.card_congr (allowedCoordinateTrue A)

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def survivingCoordinates (w : Fin 12) :
    {p : PositiveParameters F K // SurvivingParameters F K w p} ≃
      AllowedCoordinate K (rootSurvives w 0) × AllowedCoordinate F (rootSurvives w 1) ×
      AllowedCoordinate K (rootSurvives w 2) × AllowedCoordinate K (rootSurvives w 3) ×
      AllowedCoordinate F (rootSurvives w 4) × AllowedCoordinate F (rootSurvives w 5) where
  toFun p := (⟨p.val.a,p.property.1⟩,⟨p.val.b,p.property.2.1⟩,
    ⟨p.val.c,p.property.2.2.1⟩,⟨p.val.d,p.property.2.2.2.1⟩,
    ⟨p.val.u,p.property.2.2.2.2.1⟩,⟨p.val.v,p.property.2.2.2.2.2⟩)
  invFun p := ⟨⟨p.1.val,p.2.1.val,p.2.2.1.val,p.2.2.2.1.val,p.2.2.2.2.1.val,p.2.2.2.2.2.val⟩,
    ⟨p.1.property,p.2.1.property,p.2.2.1.property,p.2.2.2.1.property,
      p.2.2.2.2.1.property,p.2.2.2.2.2.property⟩⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

theorem rootSurvives_table : rootSurvives =
    ![![true,true,true,true,true,true],
      ![false,true,true,true,true,true],
      ![true,false,true,true,true,true],
      ![false,true,true,true,false,true],
      ![true,false,false,true,true,true],
      ![false,true,true,false,false,true],
      ![true,false,false,true,true,false],
      ![false,true,true,false,false,false],
      ![true,false,false,false,true,false],
      ![false,true,false,false,false,false],
      ![true,false,false,false,false,false],
      ![false,false,false,false,false,false]] := by decide

theorem card_survivingParameters (hdeg : Module.finrank F K = 3) (w : Fin 12) :
    Nat.card {p : PositiveParameters F K // SurvivingParameters F K w p} =
      Nat.card F ^ (12-weightedLength w) := by
  rw [Nat.card_congr (survivingCoordinates F K w)]
  simp only [Nat.card_prod,card_allowedCoordinate]
  rw [FiniteCubic.card_extension hdeg]
  rw [rootSurvives_table,weightedLength_table]
  fin_cases w
  · change Nat.card F^3 * (Nat.card F * (Nat.card F^3 * (Nat.card F^3 * (Nat.card F * (Nat.card F))))) = Nat.card F^12
    ring
  · change 1 * (Nat.card F * (Nat.card F^3 * (Nat.card F^3 * (Nat.card F * (Nat.card F))))) = Nat.card F^9
    ring
  · change Nat.card F^3 * (1 * (Nat.card F^3 * (Nat.card F^3 * (Nat.card F * (Nat.card F))))) = Nat.card F^11
    ring
  · change 1 * (Nat.card F * (Nat.card F^3 * (Nat.card F^3 * (1 * (Nat.card F))))) = Nat.card F^8
    ring
  · change Nat.card F^3 * (1 * (1 * (Nat.card F^3 * (Nat.card F * (Nat.card F))))) = Nat.card F^8
    ring
  · change 1 * (Nat.card F * (Nat.card F^3 * (1 * (1 * (Nat.card F))))) = Nat.card F^5
    ring
  · change Nat.card F^3 * (1 * (1 * (Nat.card F^3 * (Nat.card F * (1))))) = Nat.card F^7
    ring
  · change 1 * (Nat.card F * (Nat.card F^3 * (1 * (1 * (1))))) = Nat.card F^4
    ring
  · change Nat.card F^3 * (1 * (1 * (1 * (Nat.card F * (1))))) = Nat.card F^4
    ring
  · change 1 * (Nat.card F * (1 * (1 * (1 * (1))))) = Nat.card F^1
    ring
  · change Nat.card F^3 * (1 * (1 * (1 * (1 * (1))))) = Nat.card F^3
    ring
  · change 1 * (1 * (1 * (1 * (1 * (1))))) = Nat.card F^0
    ring

theorem card_borelIntersection (hdeg : Module.finrank F K = 3) (w : Fin 12) :
    Nat.card (borelIntersection F K hdeg w) =
      Nat.card F ^ (12-weightedLength w) * ((Nat.card F^3-1)*(Nat.card F-1)) := by
  rw [← Nat.card_congr (borelIntersectionCoordinates F K hdeg w),Nat.card_prod,
    card_survivingParameters F K hdeg w,Nat.card_prod]
  simp only [Nat.card_units]
  rw [FiniteCubic.card_extension hdeg]

end Atlas.Triality
