import Atlas.Fischer.BasicFrameGolay
import Atlas.Fischer.ParkerAlgebraRepresentation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- An arbitrary symmetry of the marked basic rays has one scalar phase and
an actual retained Golay-code permutation. -/
theorem basicFrame_scalar_golay (e : SemilinearAlgebraAutomorphism)
    (σ : Equiv.Perm Omega)
    (hσ : ∀ i, rootRay (e.val (basicAxis i)) = rootRay (basicAxis (σ i))) :
    ∃ a : Mu3, ∃ g : Mathieu24CodeModel, g.val = σ ∧
      ∀ i, e.val (u i) = a.val.val • u (g.val i) := by
  obtain ⟨a,ha⟩ := basicFrame_common_phase e σ hσ
  let f := scalarAlgebraRepresentation a⁻¹ * e
  have hf : ∀ i, f.val (basicAxis i) = basicAxis (σ i) := by
    intro i
    change scalarPhaseEquiv a⁻¹ (e.val (basicAxis i)) = _
    rw [ha i, scalarPhaseEquiv_apply, smul_smul]
    have hu : ((a⁻¹).val.val : Scalar) * a.val.val = 1 := by
      exact Units.inv_mul a.val
    rw [hu, one_smul]
  exact ⟨a, basicFrameMathieu f σ hf, rfl, basicFrame_axis_phase e σ a ha⟩

end Atlas.Fischer
