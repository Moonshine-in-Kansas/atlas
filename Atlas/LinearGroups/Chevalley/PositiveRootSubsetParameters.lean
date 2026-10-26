import Atlas.LinearGroups.Chevalley.PositiveRootSubsetCollection
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.List.Sort

/-! Unique scalar coordinates and cardinality for a cone-closed positive-root
subset. Injectivity uses the existing actual adjoint parameter recovery. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

/-- The literal chosen-family product into U_S. It is a set map, not an
additive-product group homomorphism. The list need not yet be exhaustive. -/
def positiveRootSubsetProduct (S : Set {β : ι // b.IsPos β}) (l : List S)
    (s : S → R) : positiveRootSubsetSubgroup P b O hc hm R S :=
  ⟨(l.map fun β => weightCompanionRootLiftHom P b O hc hm R
      (positiveRootChosenLift P b O hc hm R β.val) (Multiplicative.ofAdd (s β))).prod,by
    apply (positiveRootSubsetSubgroup P b O hc hm R S).list_prod_mem
    intro x hx
    obtain ⟨β,hβ,rfl⟩ := List.mem_map.mp hx
    apply positiveRootSubgroup_le_subset P b O hc hm R S β
    exact ⟨Multiplicative.ofAdd (s β),rfl⟩⟩

/-- Restricted coordinates are recovered from the full already-proved
listwise adjoint theorem, extending parameters by zero off S only in its use. -/
theorem positiveRootSubsetProduct_injective
    (S : Set {β : ι // b.IsPos β}) (l : List S) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val.val ≤ b.height γ.val.val))
    (hcover : ∀ β : S, β ∈ l) :
    Function.Injective (positiveRootSubsetProduct P b O hc hm R S l) := by
  classical
  let extend (s : S → R) (β : {β : ι // b.IsPos β}) : R :=
    if h : β ∈ S then s ⟨β,h⟩ else 0
  have hext (s : S → R) :
      positiveRootLiftProduct P b R O hc hm (positiveRootChosenLift P b O hc hm R)
        (l.map Subtype.val) (extend s) =
      (positiveRootSubsetProduct P b O hc hm R S l s).val := by
    change ((l.map Subtype.val).map fun β => weightCompanionRootLiftHom P b O hc hm R
        (positiveRootChosenLift P b O hc hm R β) (Multiplicative.ofAdd (extend s β))).prod =
      (l.map fun β => weightCompanionRootLiftHom P b O hc hm R
        (positiveRootChosenLift P b O hc hm R β.val) (Multiplicative.ofAdd (s β))).prod
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro β hβ
    simp only [Function.comp_apply,extend,dif_pos β.property]
  have hnodup' : (l.map Subtype.val).Nodup :=
    List.Nodup.map Subtype.val_injective hnodup
  have hsorted' : (l.map Subtype.val).Pairwise
      (fun β γ => b.height β.val ≤ b.height γ.val) := by
    simpa only [List.pairwise_map] using hsorted
  intro s t heq
  have hproj : weightCompanionRho P b O hc hm R
      (positiveRootLiftProduct P b R O hc hm (positiveRootChosenLift P b O hc hm R)
        (l.map Subtype.val) (extend s)) =
    weightCompanionRho P b O hc hm R
      (positiveRootLiftProduct P b R O hc hm (positiveRootChosenLift P b O hc hm R)
        (l.map Subtype.val) (extend t)) := by
    rw [hext s,hext t]
    exact congrArg (fun g : positiveRootSubsetSubgroup P b O hc hm R S =>
      weightCompanionRho P b O hc hm R g.val) heq
  have hp := positiveRootLiftProduct_parameters_eq_of_adjoint_eq P b R O hc hm
    (positiveRootChosenLift P b O hc hm R) (l.map Subtype.val)
    hnodup' hsorted' (extend s) (extend t) hproj
  funext β
  simpa only [extend,dif_pos β.property] using
    hp β.val (List.mem_map.mpr ⟨β,hcover β,rfl⟩)

theorem positiveRootSubsetProduct_surjective
    (hdiamond : SimpleDiamondProducts P b)
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (l : List S) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val.val ≤ b.height γ.val.val))
    (hcover : ∀ β : S, β ∈ l) :
    Function.Surjective (positiveRootSubsetProduct P b O hc hm R S l) := by
  intro g
  obtain ⟨s,hs⟩ := positiveRootSubset_exists_parameters P b O hc hm R hdiamond S hS
    l hnodup hsorted hcover g.val g.property
  exact ⟨s,Subtype.ext hs⟩

def positiveRootSubsetProductEquiv
    (hdiamond : SimpleDiamondProducts P b)
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S)
    (l : List S) (hnodup : l.Nodup)
    (hsorted : l.Pairwise (fun β γ => b.height β.val.val ≤ b.height γ.val.val))
    (hcover : ∀ β : S, β ∈ l) :
    (S → R) ≃ positiveRootSubsetSubgroup P b O hc hm R S :=
  Equiv.ofBijective (positiveRootSubsetProduct P b O hc hm R S l)
    ⟨positiveRootSubsetProduct_injective P b O hc hm R S l hnodup hsorted hcover,
      positiveRootSubsetProduct_surjective P b O hc hm R hdiamond S hS l hnodup hsorted hcover⟩

/-- Every finite cone-closed root subset has exactly one scalar coordinate per
root. The list is constructed locally; no group-order theorem is used. -/
theorem positiveRootSubsetSubgroup_card [Finite R]
    (hdiamond : SimpleDiamondProducts P b)
    (S : Set {β : ι // b.IsPos β}) (hS : PositiveRootConeClosed P b S) :
    Nat.card (positiveRootSubsetSubgroup P b O hc hm R S) = Nat.card R ^ Nat.card S := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  let rel : S → S → Prop := fun β γ => b.height β.val.val ≤ b.height γ.val.val
  let l : List S := (Finset.univ : Finset S).toList.mergeSort (fun β γ => decide (rel β γ))
  have hnodup : l.Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  letI : Std.Total rel := ⟨fun β γ => le_total _ _⟩
  letI : IsTrans S rel := ⟨fun β γ δ hβγ hγδ => le_trans hβγ hγδ⟩
  have hsorted : l.Pairwise rel := List.pairwise_mergeSort' rel _
  have hcover (β : S) : β ∈ l := by
    apply (List.mergeSort_perm _ _).mem_iff.mpr
    exact Finset.mem_toList.mpr (Finset.mem_univ β)
  calc
    Nat.card (positiveRootSubsetSubgroup P b O hc hm R S) = Nat.card (S → R) :=
      (Nat.card_congr (positiveRootSubsetProductEquiv P b O hc hm R hdiamond
        S hS l hnodup hsorted hcover)).symm
    _ = _ := Nat.card_fun

end Atlas.Chevalley
