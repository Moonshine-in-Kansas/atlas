import Atlas.Conway.EisensteinHexadPhaseAction
import Atlas.Codes.TernaryHexadConstantPhases

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- The actual constant codeword belonging to a constant hexad. -/
def ternaryConstantHexadCodeword (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) : TernarySixWords :=
  ⟨⟨ternaryTriadWord s,((mem_ternaryConstantHexads s).mp hs).2⟩,by
    rw [← ternarySupport_card]
    have he : ternarySupport (ternaryTriadWord s) = s := by
      ext i; simp [ternarySupport,ternaryTriadWord]
    rw [he]
    exact ((mem_ternaryConstantHexads s).mp hs).1⟩

theorem ternaryConstantHexadCodeword_support (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) :
    ternarySupport (ternaryConstantHexadCodeword s hs).val.val = s := by
  ext i; simp [ternaryConstantHexadCodeword,ternarySupport,ternaryTriadWord]

local instance : MulAction (Multiplicative ternaryGolay) EisensteinFrame :=
  MulAction.compHom EisensteinFrame eisensteinPhaseIsometries

/-- Its actual phase stabilizer has nine elements, by the uniform code restriction theorem. -/
theorem eisensteinHexadPhaseStabilizer_card (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) :
    Nat.card (MulAction.stabilizer (Multiplicative ternaryGolay)
      (eisensteinHexadFrame s hs i hi)) = 9 := by
  let c := ternaryConstantHexadCodeword s hs
  have hiff (t : Multiplicative ternaryGolay) :
      t ∈ MulAction.stabilizer (Multiplicative ternaryGolay) (eisensteinHexadFrame s hs i hi) ↔
        t.toAdd ∈ ternaryHexadConstantCode c := by
    change eisensteinPhaseIsometries (Multiplicative.ofAdd t.toAdd) • eisensteinHexadFrame s hs i hi = _ ↔ _
    rw [eisensteinHexadFrame_phase_stabilizer]
    change (∀ j ∈ s, t.toAdd.val j = t.toAdd.val i) ↔
      ∃ a : ZMod 3, ∀ j : ternarySupport c.val.val, t.toAdd.val j.val = a
    rw [show ternarySupport c.val.val=s from ternaryConstantHexadCodeword_support s hs]
    constructor
    · intro h; exact ⟨t.toAdd.val i,fun j => h j.val j.property⟩
    · rintro ⟨a,ha⟩ j hj
      exact (ha ⟨j,hj⟩).trans (ha ⟨i,hi⟩).symm
  let e : MulAction.stabilizer (Multiplicative ternaryGolay) (eisensteinHexadFrame s hs i hi) ≃
      ternaryHexadConstantCode c :=
    { toFun := fun t => ⟨t.val.toAdd,(hiff t.val).mp t.property⟩
      invFun := fun t => ⟨Multiplicative.ofAdd t.val,(hiff _).mpr t.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,ternaryHexadConstantCode_card]

/-- Each fixed complementary-hexad partition gives exactly eighty-one actual frames. -/
theorem eisensteinHexadPhaseOrbit_card (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) :
    Nat.card (MulAction.orbit (Multiplicative ternaryGolay) (eisensteinHexadFrame s hs i hi)) = 81 := by
  classical
  letI : Fintype (Multiplicative ternaryGolay) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit (Multiplicative ternaryGolay) (eisensteinHexadFrame s hs i hi)) :=
    Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (Multiplicative ternaryGolay) (eisensteinHexadFrame s hs i hi)) :=
    Fintype.ofFinite _
  have he := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (Multiplicative ternaryGolay) (eisensteinHexadFrame s hs i hi)
  simp only [← Nat.card_eq_fintype_card] at he
  rw [eisensteinHexadPhaseStabilizer_card] at he
  have hc : Nat.card (Multiplicative ternaryGolay) = 729 := by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact ternaryGolay_card
  rw [hc] at he
  omega

end Atlas.Conway
