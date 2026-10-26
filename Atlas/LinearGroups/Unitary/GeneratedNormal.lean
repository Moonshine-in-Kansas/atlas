import Atlas.LinearGroups.Unitary.IsotropicTransport

/-! Normality of the genuinely generated transvection subgroup, before any
claim that this subgroup exhausts the special unitary matrix group. -/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

instance transvectionGenerated_normal (hdeg : Module.finrank F K = 2) :
    (transvectionGenerated hdeg (n := n)).Normal where
  conj_mem x hx g := by
    have hle : transvectionGenerated hdeg ≤
        (transvectionGenerated hdeg).comap (MulAut.conj g).toMonoidHom := by
      apply iSup_le
      intro v
      apply iSup_le
      intro hv
      intro y hy
      obtain ⟨a, rfl⟩ := hy
      change g * transvection hdeg v a.toAdd.val hv
        ((trace_zero_iff hdeg _).mp a.toAdd.prop) * g⁻¹ ∈ transvectionGenerated hdeg
      rw [transvection_conjugate]
      exact transvection_mem_generated hdeg _ _ _ _
    exact hle hx
end Atlas.Unitary
