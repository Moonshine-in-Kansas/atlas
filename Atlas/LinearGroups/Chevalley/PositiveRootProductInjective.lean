import Atlas.LinearGroups.Chevalley.PositiveRootFirstParameter

/-! Injectivity for a fixed height-ordered list of distinct witnessed positive
root families. Only cancellation in the actual adjoint group is used. The image
is not asserted to be a subgroup, nor are different witness choices identified. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R] [Nontrivial R]
  (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (L : ∀ β : {β : ι // b.IsPos β}, WeightCompanionRootLift P b O hclosed hmin R β.val)

/-- Equality after the actual adjoint projection recovers all parameters
occurring in a distinct height-ordered list. Parameters outside the list are
deliberately not constrained by this statement. -/
theorem positiveRootLiftProduct_parameters_eq_of_adjoint_eq
    (l : List {β : ι // b.IsPos β}) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val ≤ b.height γ.val))
    (s t : {β : ι // b.IsPos β} → R)
    (heq : weightCompanionRho P b O hclosed hmin R
        (positiveRootLiftProduct P b R O hclosed hmin L l s) =
      weightCompanionRho P b O hclosed hmin R
        (positiveRootLiftProduct P b R O hclosed hmin L l t)) :
    ∀ β ∈ l, s β = t β := by
  revert hnodup hsorted s t heq
  induction l with
  | nil =>
    intro hnodup hsorted s t heq β hβ
    simp only [List.not_mem_nil] at hβ
  | cons β l ih =>
    intro hnodup hsorted s t heq
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hnodup
    obtain ⟨hheight, hsorted⟩ := List.pairwise_cons.mp hsorted
    have hhead := positiveRootLiftProduct_first_parameter_of_adjoint_eq
      P b R O hclosed hmin L β l hnot hheight s t heq
    have htail : weightCompanionRho P b O hclosed hmin R
        (positiveRootLiftProduct P b R O hclosed hmin L l s) =
      weightCompanionRho P b O hclosed hmin R
        (positiveRootLiftProduct P b R O hclosed hmin L l t) := by
      change weightCompanionRho P b O hclosed hmin R
        (weightCompanionRootLiftHom P b O hclosed hmin R (L β) (Multiplicative.ofAdd (s β)) *
          positiveRootLiftProduct P b R O hclosed hmin L l s) =
        weightCompanionRho P b O hclosed hmin R
        (weightCompanionRootLiftHom P b O hclosed hmin R (L β) (Multiplicative.ofAdd (t β)) *
          positiveRootLiftProduct P b R O hclosed hmin L l t) at heq
      simp only [map_mul, hhead] at heq
      exact mul_left_cancel heq
    have hrest := ih hnodup hsorted s t htail
    intro γ hγ
    rcases List.mem_cons.mp hγ with rfl | hγ
    · exact hhead
    · exact hrest γ hγ

/-- A complete distinct height-ordered positive-root list gives an injective
parameter map already on the adjoint image, with its fixed witnesses explicit. -/
theorem positiveRootLiftProduct_adjoint_injective
    (l : List {β : ι // b.IsPos β}) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val ≤ b.height γ.val))
    (hcover : ∀ β : {β : ι // b.IsPos β}, β ∈ l) :
    Function.Injective (fun s : {β : ι // b.IsPos β} → R =>
      weightCompanionRho P b O hclosed hmin R
        (positiveRootLiftProduct P b R O hclosed hmin L l s)) := by
  intro s t heq
  funext β
  exact positiveRootLiftProduct_parameters_eq_of_adjoint_eq P b R O hclosed hmin L
    l hnodup hsorted s t heq β (hcover β)

/-- The actual companion-group products have unique coordinates for this fixed
complete ordered list. This does not assert collection or root-choice coherence. -/
theorem positiveRootLiftProduct_injective
    (l : List {β : ι // b.IsPos β}) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val ≤ b.height γ.val))
    (hcover : ∀ β : {β : ι // b.IsPos β}, β ∈ l) :
    Function.Injective (positiveRootLiftProduct P b R O hclosed hmin L l) := by
  intro s t heq
  apply positiveRootLiftProduct_adjoint_injective P b R O hclosed hmin L
    l hnodup hsorted hcover
  exact congrArg (weightCompanionRho P b O hclosed hmin R) heq

end Atlas.Chevalley
