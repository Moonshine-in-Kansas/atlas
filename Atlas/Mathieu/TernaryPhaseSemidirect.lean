import Atlas.Mathieu.TernaryPhaseRepresentation
import Atlas.GroupTheory.SemidirectPerfect
import Atlas.GroupTheory.AffineNormal
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Equiv.TypeTags

noncomputable section
namespace Atlas.Codes

def ternaryPhaseMultiplicativeAction : TernaryPureAutomorphism →*
    MulAut (Multiplicative TernaryPhaseModule) where
  toFun g := AddEquiv.toMultiplicative (ternaryPurePhaseLinearHom g).toAddEquiv
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd
      (congrArg (fun e : TernaryPhaseModule ≃ₗ[ZMod 3] TernaryPhaseModule => e v.toAdd)
        (map_one ternaryPurePhaseLinearHom))
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd
      (congrArg (fun e : TernaryPhaseModule ≃ₗ[ZMod 3] TernaryPhaseModule => e v.toAdd)
        (map_mul ternaryPurePhaseLinearHom g h))

/-- The code-theoretic local semidirect product. Its identification with a full
lattice-frame stabilizer is a separate geometric obligation. -/
abbrev TernaryLocalPhaseGroup :=
  Multiplicative TernaryPhaseModule ⋊[ternaryPhaseMultiplicativeAction] TernaryPureAutomorphism

theorem ternaryPhaseModule_card : Nat.card TernaryPhaseModule = 243 := by
  letI : Fintype TernaryPhaseModule := Fintype.ofEquiv
    (Fin (Module.finrank (ZMod 3) TernaryPhaseModule) → ZMod 3)
    (Module.finBasis (ZMod 3) TernaryPhaseModule).equivFun.symm.toEquiv
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3),
    ZMod.card, ternaryPhaseModule_finrank]
  norm_num

theorem ternaryLocalPhaseGroup_order : Nat.card TernaryLocalPhaseGroup = 1924560 := by
  rw [SemidirectProduct.card]
  have hc : Nat.card (Multiplicative TernaryPhaseModule) = 243 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative TernaryPhaseModule ≃ TernaryPhaseModule)).trans
      ternaryPhaseModule_card
  rw [hc,ternaryPureAutomorphism_order]

theorem ternaryLocalPhaseGroup_perfect : Group.IsPerfect TernaryLocalPhaseGroup := by
  letI := ternaryPureAutomorphism_perfect
  apply Atlas.GroupTheory.semidirect_isPerfect_of_action_differences
  intro n
  obtain ⟨g,hg⟩ := ternaryPhase_action_difference_surjective
  obtain ⟨v,hv⟩ := hg n.toAdd
  refine ⟨g,Multiplicative.ofAdd v,?_⟩
  apply Multiplicative.toAdd.injective
  change ternaryPurePhaseEnd g v + -v = n.toAdd
  simpa only [sub_eq_add_neg] using hv

theorem ternaryPhaseMultiplicativeAction_injective :
    Function.Injective ternaryPhaseMultiplicativeAction := by
  intro g h he
  apply ternaryPurePhaseLinearHom_injective
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun e : MulAut (Multiplicative TernaryPhaseModule) =>
    (e (Multiplicative.ofAdd v)).toAdd) he

def ternaryLocalPhaseNormal : Subgroup TernaryLocalPhaseGroup :=
  (SemidirectProduct.inl : Multiplicative TernaryPhaseModule →* TernaryLocalPhaseGroup).range

theorem ternaryLocalPhase_centralizer :
    Subgroup.centralizer (ternaryLocalPhaseNormal : Set TernaryLocalPhaseGroup) =
      ternaryLocalPhaseNormal :=
  Atlas.GroupTheory.affine_centralizer _ ternaryPhaseMultiplicativeAction_injective

theorem ternaryPhase_invariant_subgroup (V : Subgroup (Multiplicative TernaryPhaseModule))
    (hV : ∀ g v, v ∈ V → ternaryPhaseMultiplicativeAction g v ∈ V) :
    V = ⊥ ∨ V = ⊤ := by
  let A : AddSubgroup TernaryPhaseModule :=
    { carrier := {v | Multiplicative.ofAdd v ∈ V}
      zero_mem' := V.one_mem
      add_mem' := V.mul_mem
      neg_mem' := V.inv_mem }
  let W := AddSubgroup.toZModSubmodule 3 A
  have hW : ∀ g : TernaryPureAutomorphism, ∀ v ∈ W, ternaryPurePhaseEnd g v ∈ W := by
    intro g v hv
    exact hV g (Multiplicative.ofAdd v) hv
  rcases ternaryPhase_invariant_eq_bot_or_top W hW with h | h
  · left
    apply le_antisymm _ bot_le
    intro v hv
    have hm : v.toAdd ∈ W := hv
    rw [h] at hm
    exact hm
  · right
    apply top_unique
    intro v _
    have hm : v.toAdd ∈ W := by rw [h]; trivial
    exact hm

theorem ternaryLocalPhase_normal_subgroups (N : Subgroup TernaryLocalPhaseGroup) [N.Normal] :
    N = ⊥ ∨ N = ternaryLocalPhaseNormal ∨ N = ⊤ := by
  letI := ternaryPureAutomorphism_simple
  exact Atlas.GroupTheory.affine_normal_subgroups _ ternaryPhaseMultiplicativeAction_injective
    ternaryPhase_invariant_subgroup N

end Atlas.Codes
