import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.SetTheory.Cardinal.NatCard

namespace Atlas.GroupTheory
variable {G H : Type*} [Group G] [Group H]

theorem normal_forms_transport (e : G ≃* H) (V : Subgroup H)
    (forms : ∀ W : Subgroup H, W.Normal → W = ⊥ ∨ W = V ∨ W = ⊤)
    (W : Subgroup G) (hW : W.Normal) :
    W = ⊥ ∨ W = V.comap e.toMonoidHom ∨ W = ⊤ := by
  have hnormal := hW.map e.toMonoidHom e.surjective
  rcases forms (W.map e.toMonoidHom) hnormal with hb | hv | ht
  · left
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using hb
  · right; left
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
    exact hv
  · right; right
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa using ht

theorem card_comap_equiv (e : G ≃* H) (V : Subgroup H) :
    Nat.card (V.comap e.toMonoidHom) = Nat.card V := by
  have h := Nat.card_congr ((V.comap e.toMonoidHom).equivMapOfInjective
    e.toMonoidHom e.injective).toEquiv
  rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective] at h

theorem no_injective_perm_transport (e : G ≃* H) (X : Type*)
    (hH : ∀ ρ : H →* Equiv.Perm X, ¬ Function.Injective ρ)
    (ρ : G →* Equiv.Perm X) : ¬ Function.Injective ρ := by
  intro hρ
  exact hH (ρ.comp e.symm.toMonoidHom) (hρ.comp e.symm.injective)

end Atlas.GroupTheory
