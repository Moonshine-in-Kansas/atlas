import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Prod

/-! character counts for the actual lattice quotients.
These are character groups, not assertions about Chevalley group centers. -/
noncomputable section
namespace Atlas.GroupTheory

theorem cyclicHom_card (A G : Type*) [CommGroup A] [IsCyclic A]
    [CommGroup G] [IsCyclic G] [Finite G] :
    Nat.card (A →* G) = Nat.gcd (Nat.card G) (Nat.card A) := by
  let : IsCyclic Gˣ := isCyclic_of_surjective
    (toUnits (G := G)).toMonoidHom (toUnits (G := G)).surjective
  rw [Nat.card_congr (IsCyclic.monoidHom_mulEquiv_rootsOfUnity A G).some.toEquiv,
    rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker,
    ← Nat.card_congr (toUnits (G := G)).toEquiv]

theorem cyclicFieldCharacters_card (A K : Type*) [CommGroup A] [IsCyclic A]
    [Field K] [Fintype K] :
    Nat.card (A →* Kˣ) = Nat.gcd (Nat.card A) (Fintype.card K - 1) := by
  rw [cyclicHom_card, Nat.card_units, Nat.card_eq_fintype_card, Nat.gcd_comm]

theorem zmodFieldCharacters_card (n : ℕ) (K : Type*) [Field K] [Fintype K] :
    Nat.card (Multiplicative (ZMod n) →* Kˣ) = Nat.gcd n (Fintype.card K - 1) := by
  rw [cyclicFieldCharacters_card]
  have h : Nat.card (Multiplicative (ZMod n)) = n := by
    change Nat.card (ZMod n) = n
    exact Nat.card_zmod n
  rw [h]

theorem characters_card_of_addEquiv_zmod {A : Type*} [AddCommGroup A]
    (n : ℕ) (e : A ≃+ ZMod n) (K : Type*) [Field K] [Fintype K] :
    Nat.card (Multiplicative A →* Kˣ) = Nat.gcd n (Fintype.card K - 1) := by
  rw [Nat.card_congr (e.toMultiplicative.monoidHomCongrLeftEquiv (N := Kˣ))]
  exact zmodFieldCharacters_card n K

def productHomEquiv (A B G : Type*) [Monoid A] [Monoid B] [CommMonoid G] :
    ((A × B) →* G) ≃ ((A →* G) × (B →* G)) where
  toFun f := (f.comp (MonoidHom.inl A B), f.comp (MonoidHom.inr A B))
  invFun p := p.1.coprod p.2
  left_inv f := MonoidHom.coprod_unique f
  right_inv := by rintro ⟨f,g⟩; simp

theorem characters_card_of_addEquiv_zmod_prod {A : Type*} [AddCommGroup A]
    (m n : ℕ) (e : A ≃+ (ZMod m × ZMod n)) (K : Type*) [Field K] [Fintype K] :
    Nat.card (Multiplicative A →* Kˣ) =
      Nat.gcd m (Fintype.card K - 1) * Nat.gcd n (Fintype.card K - 1) := by
  let f := e.toMultiplicative.trans (MulEquiv.prodMultiplicative (G := ZMod m) (H := ZMod n))
  rw [Nat.card_congr (f.monoidHomCongrLeftEquiv (N := Kˣ)),
    Nat.card_congr (productHomEquiv (Multiplicative (ZMod m)) (Multiplicative (ZMod n)) Kˣ),
    Nat.card_prod, zmodFieldCharacters_card, zmodFieldCharacters_card]

end Atlas.GroupTheory
