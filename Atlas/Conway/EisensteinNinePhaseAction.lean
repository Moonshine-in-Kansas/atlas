import Atlas.Lattices.EisensteinNinePhaseKernel
import Atlas.Lattices.EisensteinHexadPhaseClass
import Atlas.Conway.EisensteinHexadPhaseAction
import Atlas.Conway.EisensteinProjectiveAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- Global code phases fix every intrinsic frame, by the verified scalar action. -/
theorem eisensteinGlobalPhase_frame (t : ternaryGolay) (b : ZMod 3)
    (ht : ∀ i,t.val i=b) (F : EisensteinFrame) :
    eisensteinPhaseIsometries (Multiplicative.ofAdd t) • F=F := by
  have he : eisensteinPhaseIsometries (Multiplicative.ofAdd t) =
      eisensteinUnitIsometries (eisensteinSignedPhaseUnit false b) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    rw [eisensteinUnitIsometries_apply]
    funext i
    change eisensteinToRational (eisensteinPhase (t.val i))*z i =
      eisensteinToRational (eisensteinSignedPhase false b)*z i
    rw [ht]
    rfl
  rw [he,eisensteinUnitIsometries_frame]

/-- For an actual norm-nine/hexad short vector, fixing its intrinsic frame by a
code phase is equivalent to being a global scalar phase. -/
theorem eisensteinNine_frame_phase_kernel (x : EisensteinShell 6) (c : TernarySixWords)
    (u : EisensteinCoordinates) (hu : x.val.val=eisensteinTheta • u)
    (hc : eisensteinWordResidue u=c.val.val) (j : Fin 12)
    (hj : j ∉ ternarySupport c.val.val) (a : Eisensteinˣ)
    (huj : u j=eisensteinTheta*(a : Eisenstein))
    (hz : ∀ i,i ∉ ternarySupport c.val.val → i≠j → u i=0)
    (t : ternaryGolay) :
    eisensteinPhaseIsometries (Multiplicative.ofAdd t) • eisensteinFrameOfVector x =
      eisensteinFrameOfVector x ↔ ∃ b : ZMod 3,∀ i,t.val i=b := by
  have huL : eisensteinTheta • u ∈ eisensteinLeechModule := hu ▸ x.val.property
  let z : EisensteinLattice := ⟨eisensteinTheta • u,huL⟩
  let w : EisensteinLattice :=
    ⟨eisensteinDiagonal t.val (eisensteinTheta • u),eisensteinDiagonal_mem t huL⟩
  have hx : x.val=z := Subtype.ext hu
  have hy : eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) x.val=w := by
    apply Subtype.ext
    rw [eisensteinIntegralAction_phase,hu]
  constructor
  · intro h
    rw [eisensteinFrameAction_vector] at h
    have hp := congrArg Subtype.val h
    change eisensteinFramePair (eisensteinClass (eisensteinIntegralAction
      (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) x.val)) =
        eisensteinFramePair (eisensteinClass x.val) at hp
    rw [hy,hx,eisensteinFramePair_eq_iff] at hp
    rcases hp with hp|hp
    · exact eisensteinNine_phase_class_kernel c u huL hc j hj a huj hz t hp.symm
    · have hn : eisensteinClass z= -eisensteinClass w := by rw [hp]; simp
      exact (eisensteinHexad_phase_not_opposite c u huL hc t hn).elim
  · rintro ⟨b,hb⟩
    exact eisensteinGlobalPhase_frame t b hb _

end Atlas.Conway
