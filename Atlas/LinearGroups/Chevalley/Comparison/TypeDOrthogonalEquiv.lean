import Atlas.LinearGroups.Chevalley.Comparison.TypeDNaturalInjective
import Atlas.LinearGroups.Chevalley.ModelDOrder
import Atlas.LinearGroups.Orthogonal.DFamily

/-! The actual finite-field D Model is isomorphic to the existing DPlus carrier.
The map is the literal descended natural representation. Injectivity was proved
from the new Model simplicity; independent old/new order calculations now give
surjectivity. No old simplicity or order-only recognition is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeD
open Atlas.Orthogonal

/-- Equality of independent cardinality formulas, without using a comparison map. -/
theorem model_D_card_eq_DPlus_card (r : ℕ) (hr : 4≤r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (Model (.D r hr) K)=Nat.card (DPlus r K) := by
  rw [model_D_card,DPlus_card r hr]
  rfl

theorem modelNaturalProjectiveHom_bijective (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] [Finite K] :
    Function.Bijective (modelNaturalProjectiveHom n hn K) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨modelNaturalProjectiveHom_injective n hn K,
    model_D_card_eq_DPlus_card (n+2) hn K⟩

/-- The comparison equivalence has exactly the previously constructed natural map. -/
def modelNaturalProjectiveEquiv (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] [Finite K] :
    Model (.D (n+2) hn) K ≃* DPlus (n+2) K :=
  MulEquiv.ofBijective (modelNaturalProjectiveHom n hn K)
    (modelNaturalProjectiveHom_bijective n hn K)

@[simp] theorem modelNaturalProjectiveEquiv_apply (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] [Finite K] (g : Model (.D (n+2) hn) K) :
    modelNaturalProjectiveEquiv n hn K g=modelNaturalProjectiveHom n hn K g := rfl

theorem modelNaturalProjectiveEquiv_X (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] [Finite K] (i : Fin (n+2)) (t : K) :
    modelNaturalProjectiveEquiv n hn K (modelX (.D (n+2) hn) K i t) =
      naturalProjectiveHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K i t) :=
  modelNaturalProjectiveHom_X n hn K i t

theorem modelNaturalProjectiveEquiv_Y (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] [Finite K] (i : Fin (n+2)) (t : K) :
    modelNaturalProjectiveEquiv n hn K (modelY (.D (n+2) hn) K i t) =
      naturalProjectiveHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K i t) :=
  modelNaturalProjectiveHom_Y n hn K i t

/-- Public rank convention r≥4, including every finite characteristic. -/
def modelDPlusEquiv (r : ℕ) (hr : 4≤r) (K : Type*) [Field K] [Finite K] :
    Model (.D r hr) K ≃* DPlus r K := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ n => exact modelNaturalProjectiveEquiv n hr K

end Atlas.Chevalley.Comparison.TypeD
