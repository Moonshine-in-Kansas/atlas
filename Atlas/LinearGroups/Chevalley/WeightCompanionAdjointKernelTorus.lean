import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusAdjointKernel
import Atlas.LinearGroups.Chevalley.PositiveWitnessedWeylCellCoverage

/-! The full adjoint kernel lies in the literal torus over any field.
The proof uses actual B-N-B coverage and actual N/T, not a center identification,
group order, recognition theorem or an assumed simply connected label. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K]

theorem weightCompanion_rhoKernel_le_torus
    (hdiamond : SimpleDiamondProducts P b) :
    (weightCompanionRho P b O hc hm K).ker ≤ weightCompanionTorusSubgroup P b O hc hm K := by
  intro g hg
  let B := positiveWitnessedTorusJoin P b O hc hm K
  obtain ⟨n,a,c,ha,hc',hfactor⟩ :=
    weightCompanion_exists_positiveWitnessed_mul_N_mul P b O hc hm K hdiamond g
  have hker : weightCompanionRho P b O hc hm K a *
      weightCompanionRho P b O hc hm K n.val * weightCompanionRho P b O hc hm K c = 1 := by
    rw [← map_mul,← map_mul,← hfactor]
    exact hg
  have heq : weightCompanionRho P b O hc hm K n.val =
      weightCompanionRho P b O hc hm K (a⁻¹*c⁻¹) := by
    rw [map_mul,map_inv,map_inv]
    calc
      weightCompanionRho P b O hc hm K n.val =
          (weightCompanionRho P b O hc hm K a)⁻¹ *
          (weightCompanionRho P b O hc hm K a *
            weightCompanionRho P b O hc hm K n.val * weightCompanionRho P b O hc hm K c) *
          (weightCompanionRho P b O hc hm K c)⁻¹ := by group
      _ = _ := by rw [hker]; group
  have hnT := weightCompanionN_mem_torus_of_rho_eq_B P b O hc hm K hdiamond n
    (a⁻¹*c⁻¹) (B.mul_mem (B.inv_mem ha) (B.inv_mem hc')) heq
  have hTB : weightCompanionTorusSubgroup P b O hc hm K ≤ B := le_sup_right
  have hgB : g ∈ B := by
    rw [hfactor]
    exact B.mul_mem (B.mul_mem ha (hTB hnT)) hc'
  exact positiveWitnessedTorusJoin_inf_rhoKernel_le_torus P b O hc hm K hdiamond ⟨hgB,hg⟩

/-- The global projection kernel is exactly the already literal torus-kernel
intersection. Identifying this subgroup with the full center is separate. -/
theorem weightCompanion_rhoKernel_eq_torus_inf_kernel
    (hdiamond : SimpleDiamondProducts P b) :
    (weightCompanionRho P b O hc hm K).ker = weightCompanionTorusSubgroup P b O hc hm K ⊓
      (weightCompanionRho P b O hc hm K).ker := by
  exact (inf_eq_right.mpr (weightCompanion_rhoKernel_le_torus P b O hc hm K hdiamond)).symm

end Atlas.Chevalley
