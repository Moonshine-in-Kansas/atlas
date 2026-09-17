import Atlas.GroupTheory.NormalOrbitDivisibility
import Atlas.Conway.EisensteinLocalSignedPhases
import Atlas.Conway.EisensteinNineSignWitnesses
import Atlas.Conway.EisensteinUnitFrameCount

set_option maxHeartbeats 200000
set_option Elab.async false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

attribute [local instance] eisensteinNineSignPhaseAction

theorem eisensteinPhase_orbit_card_dvd_local (F : EisensteinFrame) :
    Nat.card (orbit (Multiplicative ternaryGolay) F) ∣
      Nat.card (orbit eisensteinCoordinateFrameStabilizer F) := by
  have h := Atlas.GroupTheory.normal_orbit_card_dvd eisensteinLocalSignedPhases F
  rwa [eisensteinLocalSignedPhases_orbit] at h

theorem eisensteinNineHexadFamily_phase_card (b : ZMod 3) (hb : b≠0)
    (F : EisensteinFrame) (hF : F ∈ eisensteinNineHexadFamily b hb) :
    Nat.card (orbit (Multiplicative ternaryGolay) F)=243 := by
  have hs : EisensteinNineSignFrame b F := eisensteinNineHexadFamily_sign b hb F hF
  exact eisensteinNineSignFrame_phase_orbit_card b hb F hs

/-- A243-point phase orbit cannot meet a full local orbit whose size is not
divisible by243. This also applies to noncanonical norm-nine representatives. -/
theorem eisenstein_phase243_not_mem_local_orbit (F G : EisensteinFrame)
    (hF : Nat.card (orbit (Multiplicative ternaryGolay) F)=243)
    (hG : ¬ 243 ∣ Nat.card (orbit eisensteinCoordinateFrameStabilizer G)) :
    F ∉ orbit eisensteinCoordinateFrameStabilizer G := by
  intro hmem
  have hd := eisensteinPhase_orbit_card_dvd_local F
  have he : orbit eisensteinCoordinateFrameStabilizer F =
      orbit eisensteinCoordinateFrameStabilizer G := (orbit_eq_iff (G := eisensteinCoordinateFrameStabilizer)).mpr hmem
  rw [hF,he] at hd
  exact hG hd

theorem eisensteinNineHexadFamily_disjoint_local_orbit (b : ZMod 3) (hb : b≠0)
    (G : EisensteinFrame) (hG : ¬ 243 ∣ Nat.card (orbit eisensteinCoordinateFrameStabilizer G)) :
    Disjoint (↑(eisensteinNineHexadFamily b hb) : Set EisensteinFrame)
      (orbit eisensteinCoordinateFrameStabilizer G) := by
  apply Set.disjoint_left.mpr
  intro F hF hmem
  exact eisenstein_phase243_not_mem_local_orbit F G
    (eisensteinNineHexadFamily_phase_card b hb F hF) hG hmem

theorem eisensteinNineHexadFamily_not_unit (b : ZMod 3) (hb : b≠0)
    (F : EisensteinFrame) (hF : F ∈ eisensteinNineHexadFamily b hb) :
    F ∉ eisensteinUnitResidueFrames := by
  have hsF : EisensteinNineSignFrame b F := eisensteinNineHexadFamily_sign b hb F hF
  obtain ⟨s,hs,k,hk,z,t,ht,x,hx,rfl⟩ := hsF
  rw [eisensteinFrame_unitResidue_iff]
  have hr : eisensteinResidue (x.val.val 0)=0 := by
    rw [hx]
    change eisensteinResidue (eisensteinTheta * eisensteinConstantNineForm s k b z t 0)=0
    simp [show eisensteinResidue eisensteinTheta=0 by decide +kernel]
  exact fun h => h hr

theorem eisensteinNineHexadFamily_unit_disjoint (b : ZMod 3) (hb : b≠0) :
    Disjoint (↑(eisensteinNineHexadFamily b hb) : Set EisensteinFrame) eisensteinUnitResidueFrames := by
  exact Set.disjoint_left.mpr (fun F hF hU => eisensteinNineHexadFamily_not_unit b hb F hF hU)

end Atlas.Conway
