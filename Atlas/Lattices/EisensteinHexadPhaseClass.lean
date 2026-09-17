import Atlas.Lattices.EisensteinThetaClassResidue
import Atlas.Lattices.EisensteinPhases
import Atlas.Codes.TernarySixConstants

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

theorem eisensteinDiagonal_theta (t : TernaryWord) (u : EisensteinCoordinates) :
    eisensteinDiagonal t (eisensteinTheta • u)=eisensteinTheta • eisensteinDiagonal t u := by
  funext i
  change eisensteinPhase (t i)*(eisensteinTheta*u i)=eisensteinTheta*(eisensteinPhase (t i)*u i)
  ring

theorem eisensteinDiagonal_wordResidue (t : TernaryWord) (u : EisensteinCoordinates) :
    eisensteinWordResidue (eisensteinDiagonal t u)=eisensteinWordResidue u := by
  funext i
  simp [eisensteinWordResidue,eisensteinDiagonal]

/-- A code phase cannot interchange the two opposite classes of a frame whose
normalized codeword has weight six. -/
theorem eisensteinHexad_phase_not_opposite (c : TernarySixWords)
    (u : EisensteinCoordinates) (hu : eisensteinTheta • u ∈ eisensteinLeechModule)
    (hc : eisensteinWordResidue u=c.val.val) (t : ternaryGolay) :
    eisensteinClass ⟨eisensteinTheta • u,hu⟩ ≠
      -eisensteinClass ⟨eisensteinDiagonal t.val (eisensteinTheta • u),eisensteinDiagonal_mem t hu⟩ := by
  intro h
  have hv : eisensteinTheta • (-eisensteinDiagonal t.val u) ∈ eisensteinLeechModule := by
    have he : eisensteinTheta • (-eisensteinDiagonal t.val u) =
        -eisensteinDiagonal t.val (eisensteinTheta • u) := by rw [eisensteinDiagonal_theta,smul_neg]
    rw [he]
    exact eisensteinLeechModule.neg_mem (eisensteinDiagonal_mem t hu)
  have hn : (⟨eisensteinTheta • (-eisensteinDiagonal t.val u),hv⟩ : EisensteinLattice) =
      -(⟨eisensteinDiagonal t.val (eisensteinTheta • u),eisensteinDiagonal_mem t hu⟩ : EisensteinLattice) := by
    apply Subtype.ext
    simp [eisensteinDiagonal_theta,smul_neg]
  have hh : eisensteinClass ⟨eisensteinTheta • u,hu⟩ =
      eisensteinClass ⟨eisensteinTheta • (-eisensteinDiagonal t.val u),hv⟩ := by
    rw [hn,map_neg]
    exact h
  obtain ⟨a,ha⟩ := eisensteinTheta_class_residue u (-eisensteinDiagonal t.val u) hu hv hh
  apply ternarySix_not_negative_shift c a
  intro i
  have hci := congrFun hc i
  change eisensteinResidue (u i)=c.val.val i at hci
  simpa [eisensteinDiagonal,hci] using ha i

end Atlas.Lattices
