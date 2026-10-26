import Atlas.LinearGroups.Chevalley.WeightCompanionTorus

/-! Perfectness of the actual weight companion from explicit root and torus commutators. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Group Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (K : Type*) [Field K]

theorem weightCompanionX_mem_commutator_of_unit (a : Kˣ) (ha : (a : K)^2 ≠ 1)
    (i : b.support) (t : K) : weightCompanionX P b O hclosed hmin K i t ∈
      commutator (WeightCompanion P b O hclosed hmin K) := by
  apply Atlas.GroupTheory.scaled_root_mem_commutator
    (weightCompanionXHom P b O hclosed hmin K i)
    (weightCompanionTorus P b O hclosed hmin K i a) ((a : K)^2) ha
  intro s
  simpa only [weightCompanionXHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    using weightCompanionTorus_conjugate_X P b O hclosed hmin K i a s

theorem weightCompanionY_mem_commutator_of_unit (a : Kˣ) (ha : (a : K)^2 ≠ 1)
    (i : b.support) (t : K) : weightCompanionY P b O hclosed hmin K i t ∈
      commutator (WeightCompanion P b O hclosed hmin K) := by
  apply Atlas.GroupTheory.scaled_root_mem_commutator
    (weightCompanionYHom P b O hclosed hmin K i)
    (weightCompanionTorus P b O hclosed hmin K i a⁻¹) ((a : K)^2) ha
  intro s
  simpa only [weightCompanionYHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, Units.inv_eq_val_inv, inv_inv]
    using weightCompanionTorus_conjugate_Y P b O hclosed hmin K i a⁻¹ s

theorem weightCompanion_isPerfect_of_unit (a : Kˣ) (ha : (a : K)^2 ≠ 1) :
    IsPerfect (WeightCompanion P b O hclosed hmin K) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  exact weightCompanion_induction P b O hclosed hmin K
    (weightCompanionX_mem_commutator_of_unit P b O hclosed hmin K a ha)
    (weightCompanionY_mem_commutator_of_unit P b O hclosed hmin K a ha)
    (commutator _).one_mem (fun _ _ => (commutator _).mul_mem)
    (fun _ => (commutator _).inv_mem) g

theorem weightCompanion_isPerfect_of_card_gt_three [Fintype K]
    (hq : 3 < Fintype.card K) : IsPerfect (WeightCompanion P b O hclosed hmin K) := by
  obtain ⟨a,ha0,ha⟩ := Atlas.GroupTheory.exists_nonzero_sq_ne_one hq
  exact weightCompanion_isPerfect_of_unit P b O hclosed hmin K (Units.mk0 a ha0) ha
end Atlas.Chevalley
