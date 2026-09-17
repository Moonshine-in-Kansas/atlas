import Atlas.Conway.EisensteinNinePhaseAction
import Atlas.Codes.TernaryGlobalConstants

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

local instance eisensteinNinePhaseFrameAction : MulAction (Multiplicative ternaryGolay) EisensteinFrame :=
  MulAction.compHom EisensteinFrame eisensteinPhaseIsometries

/-- The actual scalar-phase stabilizer has order three for the entire norm-nine/hexad pattern. -/
theorem eisensteinNine_phase_stabilizer_card (x : EisensteinShell 6) (c : TernarySixWords)
    (u : EisensteinCoordinates) (hu : x.val.val=eisensteinTheta • u)
    (hc : eisensteinWordResidue u=c.val.val) (j : Fin 12)
    (hj : j ∉ ternarySupport c.val.val) (a : Eisensteinˣ)
    (huj : u j=eisensteinTheta*(a : Eisenstein))
    (hz : ∀ i,i ∉ ternarySupport c.val.val → i≠j → u i=0) :
    Nat.card (MulAction.stabilizer (Multiplicative ternaryGolay) (eisensteinFrameOfVector x))=3 := by
  have hiff (t : Multiplicative ternaryGolay) :
      t ∈ MulAction.stabilizer (Multiplicative ternaryGolay) (eisensteinFrameOfVector x) ↔
        t.toAdd ∈ ternaryConstants := by
    change eisensteinPhaseIsometries (Multiplicative.ofAdd t.toAdd) • eisensteinFrameOfVector x = _ ↔ _
    rw [eisensteinNine_frame_phase_kernel x c u hu hc j hj a huj hz t.toAdd,ternaryConstants_mem_iff]
  let e : MulAction.stabilizer (Multiplicative ternaryGolay) (eisensteinFrameOfVector x) ≃
      ternaryConstants :=
    { toFun := fun t => ⟨t.val.toAdd,(hiff t.val).mp t.property⟩
      invFun := fun t => ⟨Multiplicative.ofAdd t.val,(hiff _).mpr t.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,ternaryConstants_card]

/-- Every actual norm-nine/hexad frame has a code-phase orbit of243 frames. -/
theorem eisensteinNine_phase_orbit_card (x : EisensteinShell 6) (c : TernarySixWords)
    (u : EisensteinCoordinates) (hu : x.val.val=eisensteinTheta • u)
    (hc : eisensteinWordResidue u=c.val.val) (j : Fin 12)
    (hj : j ∉ ternarySupport c.val.val) (a : Eisensteinˣ)
    (huj : u j=eisensteinTheta*(a : Eisenstein))
    (hz : ∀ i,i ∉ ternarySupport c.val.val → i≠j → u i=0) :
    Nat.card (MulAction.orbit (Multiplicative ternaryGolay) (eisensteinFrameOfVector x))=243 := by
  classical
  letI : Fintype (Multiplicative ternaryGolay) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit (Multiplicative ternaryGolay) (eisensteinFrameOfVector x)) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (Multiplicative ternaryGolay) (eisensteinFrameOfVector x)) := Fintype.ofFinite _
  have he := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (Multiplicative ternaryGolay) (eisensteinFrameOfVector x)
  simp only [← Nat.card_eq_fintype_card] at he
  rw [eisensteinNine_phase_stabilizer_card x c u hu hc j hj a huj hz] at he
  have hcard : Nat.card (Multiplicative ternaryGolay)=729 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact ternaryGolay_card
  rw [hcard] at he
  omega

end Atlas.Conway
