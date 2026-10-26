import Atlas.LinearGroups.Chevalley.WeightCompanionFamilyRestriction
import Atlas.LinearGroups.Chevalley.WeightCompanionAdjointKernelTorus
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusOrder

/-! Adding minuscule blocks does not change a companion whose retained weights span P.
Only the structural torus range, integral weight spanning and actual adjoint-kernel
containment are used. No cardinality, full-center or simplicity theorem is used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N κ τ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] (e : τ → κ)

@[simp] theorem weightCompanionRestrict_torus (i : b.support) (t : Rˣ) :
    weightCompanionRestrict P b O hc hm R e (weightCompanionTorus P b O hc hm R i t) =
      weightCompanionTorus P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R i t := by
  simp only [weightCompanionTorus, weightCompanionWeyl, map_mul, map_inv,
    weightCompanionRestrict_X, weightCompanionRestrict_Y]

set_option backward.isDefEq.respectTransparency false in
theorem weightCompanionRestrict_torusProduct (s : Finset b.support) (t : b.support → Rˣ) :
    weightCompanionRestrict P b O hc hm R e (weightCompanionTorusProduct P b O hc hm R s t) =
      weightCompanionTorusProduct P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R s t := by
  induction s using Finset.induction_on with
  | empty => simp [weightCompanionTorusProduct]
  | @insert i s hi ih =>
    unfold weightCompanionTorusProduct at *
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hi,
      map_mul, weightCompanionRestrict_torus, ih]

@[simp] theorem weightCompanionRestrict_torusParameters (t : b.support → Rˣ) :
    weightCompanionRestrict P b O hc hm R e (weightCompanionTorusParameters P b O hc hm R t) =
      weightCompanionTorusParameters P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) R t :=
  weightCompanionRestrict_torusProduct P b O hc hm R e Finset.univ t

variable (K : Type*) [Field K]

/-- An element killed by forgetting lies in the actual adjoint kernel, hence in T;
its retained integral weight characters then kill all torus parameters. -/
theorem weightCompanionRestrict_injective
    (hdiamond : SimpleDiamondProducts P b)
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪
      {μ | ∃ a : τ, μ ∈ O (e a)}) = ⊤) :
    Function.Injective (weightCompanionRestrict P b O hc hm K e) := by
  apply (weightCompanionRestrict P b O hc hm K e).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  change weightCompanionRestrict P b O hc hm K e g = 1 at hg
  apply Subgroup.mem_bot.mpr
  have hrho : weightCompanionRho P b O hc hm K g = 1 := by
    have h := congrArg (weightCompanionRho P b (O ∘ e)
      (fun a => hc (e a)) (fun a => hm (e a)) K) hg
    simpa only [← MonoidHom.comp_apply, weightCompanionRestrict_rho, map_one] using h
  have hT := weightCompanion_rhoKernel_le_torus P b O hc hm K hdiamond hrho
  rw [weightCompanionTorusSubgroup_eq_range] at hT
  obtain ⟨t,rfl⟩ := hT
  have ht : weightCompanionTorusParameters P b (O ∘ e)
      (fun a => hc (e a)) (fun a => hm (e a)) K t = 1 := by
    rw [← weightCompanionRestrict_torusParameters]
    exact hg
  have ht1 := weightCompanionTorusParameters_kernel_trivial_of_span P b (O ∘ e)
    (fun a => hc (e a)) (fun a => hm (e a)) K hspan t ht
  rw [ht1, map_one]

/-- Actual enlarged and retained companions are isomorphic by literal block restriction.
This is a structural result over any field, not an order comparison. -/
def weightCompanionFamilyRestrictionEquiv
    (hdiamond : SimpleDiamondProducts P b)
    (hspan : Submodule.span ℤ (Set.range (rootWeight P) ∪
      {μ | ∃ a : τ, μ ∈ O (e a)}) = ⊤) :
    WeightCompanion P b O hc hm K ≃*
      WeightCompanion P b (O ∘ e) (fun a => hc (e a)) (fun a => hm (e a)) K :=
  MulEquiv.ofBijective (weightCompanionRestrict P b O hc hm K e)
    ⟨weightCompanionRestrict_injective P b O hc hm e K hdiamond hspan,
      weightCompanionRestrict_surjective P b O hc hm K e⟩

end Atlas.Chevalley
