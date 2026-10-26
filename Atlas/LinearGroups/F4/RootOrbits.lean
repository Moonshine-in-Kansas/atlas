import Atlas.LinearGroups.F4.RootData

/-! Orbits of the three explicitly marked B₃ reflections on the short-root labels.
These are finite root-label orbits only, not subdegrees of an F₄(F) action. -/
namespace Atlas.F4.RootData

/-- The rightmost reflection acts first. -/
def b3WordAction (w : List (Fin 3)) : Equiv.Perm Root :=
  (w.map (fun i=>simpleReflection i.castSucc)).prod

theorem b3WordAction_append (u v : List (Fin 3)) :
    b3WordAction (u++v)=b3WordAction u*b3WordAction v := by
  simp [b3WordAction,List.map_append,List.prod_append]

theorem simpleReflection_inv (i : Fin 4) : (simpleReflection i)⁻¹=simpleReflection i := by
  ext r
  rfl

theorem b3WordAction_reverse (w : List (Fin 3)) : b3WordAction w.reverse=(b3WordAction w)⁻¹ := by
  induction w with
  | nil => simp [b3WordAction]
  | cons i w ih =>
    rw [List.reverse_cons,b3WordAction_append,ih]
    simp [b3WordAction,simpleReflection_inv]

/-- Three signed-coordinate reflections preserve the first coordinate. -/
theorem b3_simple_preserves : ∀i : Fin 3,∀r : Root,
    coordinates (simpleReflection i.castSucc r) 0=coordinates r 0 ∧
    (IsShort (simpleReflection i.castSucc r) ↔ IsShort r) := by decide +kernel

theorem b3WordAction_first_coordinate (w : List (Fin 3)) (r : Root) :
    coordinates (b3WordAction w r) 0=coordinates r 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change coordinates (simpleReflection i.castSucc (b3WordAction w r)) 0=coordinates r 0
    exact ((b3_simple_preserves i _).1).trans ih

def b3Representative : Root → Root :=
  ![24,24,25,25,24,24,25,25,24,24,25,25,26,26,26,26,26,26,26,26,26,26,26,26,24,25,26,26,26,26,26,26,32,32,32,32,32,32,32,32,40,40,40,40,40,40,40,40]

def b3WitnessWord : Root → List (Fin 3) :=
  ![[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,1,2,1,0],[0],[1,2,1,0],[1,0],[2,1,0],[],[2],[1,2],[2,1,2],[0,1,2],[2,0,1,2],[1,2,0,1,2],[2,1,2,0,1,2],[],[2],[1,2],[2,1,2],[0,1,2],[2,0,1,2],[1,2,0,1,2],[2,1,2,0,1,2]]

theorem b3WitnessWord_correct : ∀r : Root,IsShort r →
    b3WordAction (b3WitnessWord r) (b3Representative r)=r := by decide +kernel

theorem b3Representative_equal : ∀r s : Root,
    coordinates r 0=coordinates s 0 → b3Representative r=b3Representative s := by decide +kernel

/-- Reachability under actual words in the three specified reflection permutations. -/
def B3Related (r s : Root) : Prop := ∃w : List (Fin 3),b3WordAction w r=s

theorem b3Related_short_iff (r s : Root) (hr : IsShort r) (hs : IsShort s) :
    B3Related r s ↔ coordinates r 0=coordinates s 0 := by
  constructor
  · rintro ⟨w,rfl⟩
    exact (b3WordAction_first_coordinate w r).symm
  · intro h
    refine ⟨b3WitnessWord s++(b3WitnessWord r).reverse,?_⟩
    rw [b3WordAction_append,b3WordAction_reverse]
    change b3WordAction (b3WitnessWord s) ((b3WordAction (b3WitnessWord r))⁻¹ r)=s
    have hi : (b3WordAction (b3WitnessWord r))⁻¹ r=b3Representative r := by
      calc
        _=(b3WordAction (b3WitnessWord r))⁻¹
            (b3WordAction (b3WitnessWord r) (b3Representative r)) :=
          congrArg (fun z=>(b3WordAction (b3WitnessWord r))⁻¹ z)
            (b3WitnessWord_correct r hr).symm
        _=b3Representative r := Equiv.symm_apply_apply _ _
    rw [hi,b3Representative_equal r s h]
    exact b3WitnessWord_correct s hs

theorem short_first_coordinate_values : ∀r : Root,IsShort r →
    coordinates r 0=2 ∨ coordinates r 0=1 ∨ coordinates r 0=0 ∨
      coordinates r 0= -1 ∨ coordinates r 0= -2 := by decide +kernel

theorem b3_short_level_counts :
    Fintype.card {r : Root // IsShort r ∧ coordinates r 0=2}=1 ∧
    Fintype.card {r : Root // IsShort r ∧ coordinates r 0=1}=8 ∧
    Fintype.card {r : Root // IsShort r ∧ coordinates r 0=0}=6 ∧
    Fintype.card {r : Root // IsShort r ∧ coordinates r 0= -1}=8 ∧
    Fintype.card {r : Root // IsShort r ∧ coordinates r 0= -2}=1 := by decide +kernel

end Atlas.F4.RootData
