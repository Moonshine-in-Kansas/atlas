import Atlas.Conway.EisensteinNineHexadFrames
import Atlas.Lattices.EisensteinConstantClassPartition

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- Code-phase related constant norm-nine frames have the same hexad partition. -/
theorem eisensteinNineHexadFrame_phase_partition (s r : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (hr : r ∈ ternaryConstantHexads)
    (k j l m : Fin 12) (hk : k ∈ s) (hj : j ∉ s) (hl : l ∈ r) (hm : m ∉ r)
    (b d : ZMod 3) (hb : b≠0) (hd : d≠0) (t : ternaryGolay)
    (h : eisensteinPhaseIsometries (Multiplicative.ofAdd t) •
        eisensteinNineHexadFrame r hr l m hl hm d hd =
      eisensteinNineHexadFrame s hs k j hk hj b hb) :
    ternaryConstantHexadPair s=ternaryConstantHexadPair r := by
  let x := eisensteinNineHexadShellVector s hs k j hk hj b hb
  let y := eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6
    (eisensteinNineHexadShellVector r hr l m hl hm d hd)
  have hy : y.val.val=eisensteinTheta •
      eisensteinDiagonal t.val (eisensteinNineHexadLift r l m d) := by
    change (eisensteinIntegralAction _ _).val=_
    rw [eisensteinIntegralAction_phase]
    exact eisensteinDiagonal_theta _ _
  have hc (a : Finset (Fin 12)) (q z : Fin 12) (e : ZMod 3) :
      eisensteinWordResidue (eisensteinNineHexadLift a q z e)=ternaryTriadWord a := by
    funext i
    by_cases hi : i ∈ a <;> simp [eisensteinWordResidue,eisensteinNineHexadLift,
      ternaryTriadWord,hi,show eisensteinResidue eisensteinTheta=0 by decide +kernel]
  have hp : eisensteinFramePair (eisensteinClass x.val)=
      eisensteinFramePair (eisensteinClass y.val) := by
    rw [eisensteinNineHexadFrame,eisensteinFrameAction_vector] at h
    exact congrArg Subtype.val h.symm
  apply eisenstein_constant_frame_partition s r x y
    (eisensteinNineHexadLift s k j b) (eisensteinDiagonal t.val (eisensteinNineHexadLift r l m d))
    rfl hy (hc s k j b) _ hp
  rw [eisensteinDiagonal_wordResidue,hc]

end Atlas.Conway
