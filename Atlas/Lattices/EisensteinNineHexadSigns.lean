import Atlas.Lattices.EisensteinNineHexadVectors
import Atlas.Lattices.EisensteinClassCoordinates
import Atlas.Lattices.EisensteinHexadPhaseClass
import Atlas.Codes.TernaryConstantHexadIsolation

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- Opposite nonzero correction choices cannot belong to the same oriented
class, even after arbitrary actual code phases. -/
theorem eisensteinNineHexad_class_sign (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b d : ZMod 3) (t : ternaryGolay)
    (hclass : eisensteinClass (eisensteinNineHexadLatticeVector s hs k j b)=
      eisensteinClass ⟨eisensteinDiagonal t.val (eisensteinNineHexadVector s k j d),
        eisensteinDiagonal_mem t (eisensteinNineHexadVector_mem s hs k j d)⟩) : b=d := by
  let v : EisensteinCoordinates := fun i =>
    (eisensteinPhaseCorrection b-eisensteinPhaseCorrection d)*
      ((if i=j then 1 else 0)-(if i=k then 1 else 0))+
    eisensteinPhaseCorrection (t.val i)*eisensteinNineHexadLift s k j d i
  have he : eisensteinNineHexadVector s k j b-
      eisensteinDiagonal t.val (eisensteinNineHexadVector s k j d)=(3 : Eisenstein) • v := by
    funext i
    change eisensteinTheta*eisensteinNineHexadLift s k j b i-
      eisensteinPhase (t.val i)*(eisensteinTheta*eisensteinNineHexadLift s k j d i)=3*v i
    rw [eisensteinPhase_correction]
    dsimp [eisensteinNineHexadLift,v]
    linear_combination
      ((eisensteinPhaseCorrection b-eisensteinPhaseCorrection d)*
        ((if i=k then (1 : Eisenstein) else 0)-(if i=j then 1 else 0))-
        eisensteinPhaseCorrection (t.val i)*
        ((if i ∈ s then 1 else 0)+eisensteinTheta*eisensteinPhaseCorrection d*
          ((if i=k then 1 else 0)-(if i=j then 1 else 0))))*eisensteinTheta_sq
  have hcode := ((eisensteinClass_difference_three_iff _ _ v he).mp hclass).1
  have hjk : j≠k := by intro h; exact hj (h ▸ hk)
  have hz := ternaryConstantHexad_isolated_coordinate s hs ⟨eisensteinWordResidue v,hcode⟩ j hj
    (by
      intro i hi hij
      have hik : i≠k := by intro h; exact hi (h ▸ hk)
      simp [eisensteinWordResidue,v,eisensteinNineHexadLift,hi,hij,hik])
  have hr : -b+d=0 := by
    simpa [eisensteinWordResidue,v,eisensteinNineHexadLift,hj,hjk,
      show eisensteinResidue eisensteinTheta=0 by decide +kernel] using hz
  linear_combination -hr

/-- A phase cannot reverse orientation between two normalized constant-hexad vectors. -/
theorem eisensteinNineHexad_class_not_negative (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b d : ZMod 3) (t : ternaryGolay) :
    eisensteinClass (eisensteinNineHexadLatticeVector s hs k j b) ≠
      -eisensteinClass ⟨eisensteinDiagonal t.val (eisensteinNineHexadVector s k j d),
        eisensteinDiagonal_mem t (eisensteinNineHexadVector_mem s hs k j d)⟩ := by
  intro h
  let u := eisensteinNineHexadLift s k j b
  let v := -eisensteinDiagonal t.val (eisensteinNineHexadLift s k j d)
  have hv : eisensteinTheta • v ∈ eisensteinLeechModule := by
    dsimp [v]
    rw [smul_neg,← eisensteinDiagonal_theta]
    exact eisensteinLeechModule.neg_mem
      (eisensteinDiagonal_mem t (eisensteinNineHexadVector_mem s hs k j d))
  have he : (⟨eisensteinTheta • v,hv⟩ : EisensteinLattice)=
      -⟨eisensteinDiagonal t.val (eisensteinNineHexadVector s k j d),
        eisensteinDiagonal_mem t (eisensteinNineHexadVector_mem s hs k j d)⟩ := by
    apply Subtype.ext
    simp only [v,eisensteinNineHexadVector,smul_neg,eisensteinDiagonal_theta,Submodule.coe_neg]
  have hh : eisensteinClass (eisensteinNineHexadLatticeVector s hs k j b)=
      eisensteinClass ⟨eisensteinTheta • v,hv⟩ := by rw [he,map_neg]; exact h
  obtain ⟨a,ha⟩ := eisensteinTheta_class_residue u v
    (eisensteinNineHexadVector_mem s hs k j b) hv hh
  have hzero : a=0 := by
    have h := ha j
    simpa [u,v,eisensteinNineHexadLift,eisensteinDiagonal,hj,
      show eisensteinResidue eisensteinTheta=0 by decide +kernel] using h.symm
  have hone : (2 : ZMod 3)=a := by
    simpa [u,v,eisensteinNineHexadLift,eisensteinDiagonal,hk,show (1 : ZMod 3)+1=2 by decide,
      show eisensteinResidue eisensteinTheta=0 by decide +kernel] using ha k
  rw [hzero] at hone
  exact (by decide : (2 : ZMod 3)≠0) hone

end Atlas.Lattices
