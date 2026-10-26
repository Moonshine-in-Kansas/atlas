import Atlas.Tits.LocalGroups
import Atlas.GroupTheory.FiniteSuborbitPrimitivity

namespace Atlas.Tits
open Atlas.Rudvalis
open scoped BigOperators

noncomputable def localPiece (i : Fin 5) : Set MinimalCross :=
  ![{referenceSecondCross},coupleFusionTen,coupleFusionEighty,coupleFusionSixForty,coupleFusionThousand] i

def localSubdegree (i : Fin 5) : ℕ := ![1,10,80,640,1024] i

theorem localPiece_card (i : Fin 5) : Nat.card (localPiece i)=localSubdegree i := by
  fin_cases i
  · simp [localPiece,localSubdegree]
  · exact coupleFusionTen_card
  · exact coupleFusionEighty_card
  · exact coupleFusionSixForty_card
  · exact coupleFusionThousand_card

theorem localPiece_orthogonal (i : Fin 5) (c : MinimalCross) (hc : c∈localPiece i) :
    CrossOrthogonal localReferenceCross c := by
  fin_cases i
  · change c=referenceSecondCross at hc
    rw [hc];exact reference_crosses_orthogonal
  · exact ((coupleFusionTen_energy c).mp hc).1.1
  · exact ((coupleFusionEighty_energy c).mp hc).1.1
  · exact ((coupleFusionSixForty_energy c).mp hc).1.1
  · exact hc.1.1

theorem localPiece_orbit (i : Fin 5) (c : MinimalCross) (hc : c∈localPiece i) :
    MulAction.orbit coupleFusionGroup c=localPiece i := by
  fin_cases i
  · change c=referenceSecondCross at hc
    rw [hc];exact coupleFusion_referenceSecond_orbit
  · exact coupleFusionTen_orbit c hc
  · exact coupleFusionEighty_orbit c hc
  · exact coupleFusionSixForty_orbit c hc
  · exact coupleFusionThousand_orbit c hc

theorem localPiece_unique (i j : Fin 5) (c : MinimalCross)
    (hi : c∈localPiece i) (hj : c∈localPiece j) : i=j := by
  have he := (localPiece_orbit i c hi).symm.trans (localPiece_orbit j c hj)
  have hn : localSubdegree i=localSubdegree j := by
    rw [←localPiece_card i,←localPiece_card j,he]
  have hinj : Function.Injective localSubdegree := by decide +kernel
  exact hinj hn

theorem localPiece_exhaustive (c : Neighbours) : ∃i : Fin 5,c.val∈localPiece i := by
  rcases coupleFusion_neighbour_partition c.val c.prop with h|h|h|h|h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩
  · exact ⟨4,h⟩

noncomputable def localLabel (c : Neighbours) : Fin 5 := Classical.choose (localPiece_exhaustive c)

theorem localLabel_mem (c : Neighbours) : c.val∈localPiece (localLabel c) :=
  Classical.choose_spec (localPiece_exhaustive c)

theorem localLabel_eq_iff (c : Neighbours) (i : Fin 5) :
    localLabel c=i ↔ c.val∈localPiece i := by
  constructor
  · rintro rfl;exact localLabel_mem c
  · exact localPiece_unique _ _ c.val (localLabel_mem c)

theorem localLabel_reference : localLabel referenceNeighbour=0 :=
  (localLabel_eq_iff _ _).mpr rfl

noncomputable def localLabelFibreEquiv (i : Fin 5) :
    {c : Neighbours // localLabel c=i} ≃ localPiece i where
  toFun c := ⟨c.val.val,(localLabel_eq_iff _ _).mp c.prop⟩
  invFun c := ⟨⟨c.val,localPiece_orthogonal i c.val c.prop⟩,(localLabel_eq_iff _ _).mpr c.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem localLabel_fibre_card (i : Fin 5) :
    Nat.card {c : Neighbours // localLabel c=i}=localSubdegree i :=
  (Nat.card_congr (localLabelFibreEquiv i)).trans (localPiece_card i)

theorem localLabel_transitive (a b : Neighbours) (h : localLabel a=localLabel b) :
    ∃g : pairStabilizer,g • a=b := by
  have he := localPiece_orbit (localLabel a) a.val (localLabel_mem a)
  have hb : b.val∈MulAction.orbit coupleFusionGroup a.val := by
    rw [he,h];exact localLabel_mem b
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hb
  exact ⟨coupleProjection g,Subtype.ext hg⟩

/-- The five subdegree sums admit no nontrivial proper block size. -/
theorem local_block_arithmetic (T : Finset (Fin 5)) (h0 : 0∈T)
    (hd : (∑i∈T,localSubdegree i)∣1755) :
    (∑i∈T,localSubdegree i)=1 ∨ (∑i∈T,localSubdegree i)=1755 := by
  have h : ∀T : Finset (Fin 5),0∈T → (∑i∈T,localSubdegree i)∣1755 →
      (∑i∈T,localSubdegree i)=1 ∨ (∑i∈T,localSubdegree i)=1755 := by decide +kernel
  exact h T h0 hd

/-- Primitivity of the actual cross stabilizer on its 1755 orthogonal crosses. -/
theorem neighboursPrimitive : MulAction.IsPreprimitive Ambient Neighbours := by
  apply Atlas.GroupTheory.primitive_of_suborbit_sums referenceNeighbour localLabel
    localLabel_transitive localSubdegree localLabel_fibre_card
  intro T hT hd
  rw [localLabel_reference] at hT
  rw [cardNeighbours] at hd ⊢
  exact local_block_arithmetic T hT hd

end Atlas.Tits
