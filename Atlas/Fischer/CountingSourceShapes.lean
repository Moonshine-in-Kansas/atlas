import Atlas.Fischer.CountingProfileEvaluation
import Atlas.Fischer.CountingSupportFibres

namespace Atlas.Fischer
open Atlas.Codes

/-- The finite geometric profiles, without the field words or pair masks. -/
abbrev CountingSourceShape := CountingSourceTypeA ⊕
  ({S : Finset (Fin 6) // S.card=4} ⊕ Fin 6)

def countingShapeProfile : CountingSourceShape → CountingColumnVector
  | .inl t => countingTypeAColumnProfile t.val
  | .inr (.inl t) => countingTypeBColumnProfile t.val
  | .inr (.inr j) => countingTypeCColumnProfile j

def countingShapeType : CountingSourceShape → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def countingShapeAdmissible : CountingSourceShape → Prop
  | .inl t => t.val ≠ countingTableD
  | .inr (.inl t) => (t.val ∩ countingTableD).card=0 ∨ (t.val ∩ countingTableD).card=2
  | .inr (.inr j) => j ∈ countingTableD

instance (s : CountingSourceShape) : Decidable (countingShapeAdmissible s) := by
  cases s with
  | inl t => exact inferInstanceAs (Decidable (t.val ≠ countingTableD))
  | inr s => cases s with
    | inl t => exact inferInstanceAs (Decidable ((t.val ∩ countingTableD).card=0 ∨
        (t.val ∩ countingTableD).card=2))
    | inr j => exact inferInstanceAs (Decidable (j ∈ countingTableD))

def countingShapeRow (trio : Bool) : CountingSourceShape → Fin 14
  | .inl t => if trio then
      (if t.val={2,3} ∨ t.val={4,5} then 7
       else if (t.val ∩ countingTableD).card=0 then 8 else 10)
    else (if t.val={0,2} ∨ t.val={1,2} then 0
      else if (t.val ∩ countingTableD).card=1 then 1 else 2)
  | .inr (.inl t) => if trio then
      (if (t.val ∩ countingTableD).card=0 then 9
       else if t.val={0,1,2,3} ∨ t.val={0,1,4,5} then 11 else 12)
    else (if (t.val ∩ countingTableD).card=0 then 3 else if 2 ∈ t.val then 4 else 5)
  | .inr (.inr _) => if trio then 13 else 6

def countingShapeMultiplicity : CountingSourceShape → ℕ
  | .inl _ => 1
  | .inr (.inl _) => 24
  | .inr (.inr _) => 64

def countingShapeData (trio : Bool) (s : CountingSourceShape) : CountingProfileData :=
  ⟨if trio then 1 else 0, countingTableD,
    if trio then {2,3} else {0,2}, if trio then {4,5} else {1,2},
    countingShapeProfile s, countingShapeType s⟩

noncomputable def countingSourceShape : CountingSourceParameters → CountingSourceShape
  | .inl t => .inl t
  | .inr (.inl t) => .inr (.inl ⟨countingHexSupport t.1.val,
      (countingHexSupport_card t.1.val).trans t.1.property⟩)
  | .inr (.inr t) => .inr (.inr t.2)

theorem countingSourceShape_profile (t : CountingSourceParameters) (i : Fin 6) :
    (countingSourceColumn t i).card=countingShapeProfile (countingSourceShape t) i := by
  classical
  rcases t with a | (b | c)
  · exact countingSourceColumn_card_A a i
  · rw [countingSourceColumn_card_B]
    simp only [countingSourceShape, countingShapeProfile, countingTypeBColumnProfile,
      countingHexSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : b.1.val.val i=0 <;> simp [h]
  · exact countingSourceColumn_card_C c i

end Atlas.Fischer
