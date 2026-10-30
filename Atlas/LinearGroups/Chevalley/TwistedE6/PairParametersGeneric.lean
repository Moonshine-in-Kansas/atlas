import Atlas.LinearGroups.Chevalley.PositiveRootFirstParameter
import Atlas.LinearGroups.Chevalley.AdjointOpposition

/-! Distinct literal simple roots have independent parameters. This continuation
is kept outside the normal root until compilation and dependency inspection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

section Generic
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R] [Nontrivial R]
  (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)

include O hc hm

/-- Distinct literal simple-root factors have independent parameters already
in the adjoint image. No global injectivity of the companion is assumed. -/
theorem adjointX_simple_pair_injective (i j : b.support) (hij : i ≠ j) :
    Function.Injective (fun p : R × R =>
      adjointX P b R i p.1 * adjointX P b R j p.2) := by
  let L (β : {β : ι // b.IsPos β}) :
      WeightCompanionRootLift P b O hc hm R β.val :=
    if h : β.val ∈ b.support then
      ⟨⟨β.val, h⟩, 1, by simp⟩
    else Classical.choice (positiveRoot_has_weightCompanionRootLift
      P b O hc hm R β.val β.property)
  have hL (k : b.support) (t : R) :
      weightCompanionRootLiftHom P b O hc hm R
        (L ⟨k.val, b.isPos_of_mem_support k.property⟩) (Multiplicative.ofAdd t) =
      weightCompanionX P b O hc hm R k t := by
    simp [L, k.property, weightCompanionRootLiftHom_apply]
  let β : {β : ι // b.IsPos β} := ⟨i.val, b.isPos_of_mem_support i.property⟩
  let γ : {β : ι // b.IsPos β} := ⟨j.val, b.isPos_of_mem_support j.property⟩
  have hijv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have hβγ : β ≠ γ := fun h => hijv (congrArg (fun x : {β : ι // b.IsPos β} => x.val) h)
  let f (p : R × R) (α : {β : ι // b.IsPos β}) :=
    if α.val = i.val then p.1 else p.2
  have hp (p : R × R) :
      weightCompanionRho P b O hc hm R
        (positiveRootLiftProduct P b R O hc hm L [β, γ] (f p)) =
      adjointX P b R i p.1 * adjointX P b R j p.2 := by
    simp only [positiveRootLiftProduct, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    change weightCompanionRho P b O hc hm R
      (weightCompanionRootLiftHom P b O hc hm R
        (L ⟨i.val, b.isPos_of_mem_support i.property⟩)
        (Multiplicative.ofAdd (if i.val = i.val then p.1 else p.2)) *
      weightCompanionRootLiftHom P b O hc hm R
        (L ⟨j.val, b.isPos_of_mem_support j.property⟩)
        (Multiplicative.ofAdd (if j.val = i.val then p.1 else p.2))) = _
    simp only [ite_true, if_neg hijv.symm, hL, map_mul, weightCompanionRho_X]
  intro s t heq
  change adjointX P b R i s.1 * adjointX P b R j s.2 =
    adjointX P b R i t.1 * adjointX P b R j t.2 at heq
  have hfirst := positiveRootLiftProduct_first_parameter_of_adjoint_eq
    P b R O hc hm L β [γ] (by simp [hβγ])
    (by
      intro α hα
      have hαγ : α = γ := by simpa using hα
      subst α
      exact le_of_eq ((b.height_one_of_mem_support i.property).trans
        (b.height_one_of_mem_support j.property).symm))
    (f s) (f t) (by rw [hp, hp]; exact heq)
  have hfst : s.1 = t.1 := by simpa [f, β] using hfirst
  apply Prod.ext hfst
  rw [hfst] at heq
  exact adjointX_injective P b R j (mul_left_cancel heq)

theorem adjointY_simple_pair_injective (i j : b.support) (hij : i ≠ j) :
    Function.Injective (fun p : R × R =>
      adjointY P b R i p.1 * adjointY P b R j p.2) := by
  intro s t h
  apply adjointX_simple_pair_injective P b R O hc hm i j hij
  simpa only [map_mul, adjointOppositionEquiv_Y] using
    congrArg (adjointOppositionEquiv P b R) h
end Generic
end Atlas.Chevalley
