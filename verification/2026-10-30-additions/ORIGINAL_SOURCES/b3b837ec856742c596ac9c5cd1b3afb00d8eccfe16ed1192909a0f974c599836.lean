import Atlas.LinearGroups.Chevalley.Comparison.G2.OctonionLift
import Atlas.LinearGroups.Chevalley.ModelG2Order
import Atlas.LinearGroups.G2.Order

/-! Actual marked equivalence of the Chevalley and full octonion models.
The map is constructed from root actions before the two independent finite
orders identify its domain and kernel. No simplicity or recognition is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.G2
open Atlas.LinearAlgebra
variable (K : Type*) [Field K] [Finite K]

theorem independent_orders_equal :
    Nat.card (Atlas.G2.Model K) = Nat.card (Model .G2 K) := by
  rw [Atlas.G2.card_Model, model_G2_card]

theorem octonionLiftSubgroup_eq_top : octonionLiftSubgroup K = ⊤ :=
  (Atlas.GroupTheory.subgroup_eq_top_and_bijective_of_surjective_of_card
    (octonionLiftSubgroup K) (octonionLiftHom K) (octonionLiftHom_surjective K)
    (independent_orders_equal K)).1

def octonionToChevalley : Atlas.G2.Model K ≃* Model .G2 K :=
  faithfulConjugationLiftEquiv (faithfulMatrixHom8 K) (gamma K) (geckRepresentation K)
    (gamma_injective K) (geckRepresentation_injective K)
    (octonionLiftHom_surjective K) (independent_orders_equal K)

def octonionEquiv : Model .G2 K ≃* Atlas.G2.Model K := (octonionToChevalley K).symm

theorem octonionToChevalley_X (i : Fin 2) (t : K) :
    octonionToChevalley K (octonionSimpleRoot K (Fin.castAdd 2 i) t) =
      modelX .G2 K i t :=
  faithfulConjugationLiftEquiv_eq (faithfulMatrixHom8 K) (gamma K) (geckRepresentation K)
    (gamma_injective K) (geckRepresentation_injective K)
    (octonionLiftHom_surjective K) (independent_orders_equal K) _ _
    (octonion_X_compatible K i t)

theorem octonionToChevalley_Y (i : Fin 2) (t : K) :
    octonionToChevalley K (octonionSimpleRoot K (Fin.natAdd 2 i) t) =
      modelY .G2 K i t :=
  faithfulConjugationLiftEquiv_eq (faithfulMatrixHom8 K) (gamma K) (geckRepresentation K)
    (gamma_injective K) (geckRepresentation_injective K)
    (octonionLiftHom_surjective K) (independent_orders_equal K) _ _
    (octonion_Y_compatible K i t)

theorem octonionEquiv_X (i : Fin 2) (t : K) :
    octonionEquiv K (modelX .G2 K i t) =
      octonionSimpleRoot K (Fin.castAdd 2 i) t :=
  (MulEquiv.symm_apply_eq (octonionToChevalley K)).mpr (octonionToChevalley_X K i t).symm

theorem octonionEquiv_Y (i : Fin 2) (t : K) :
    octonionEquiv K (modelY .G2 K i t) =
      octonionSimpleRoot K (Fin.natAdd 2 i) t :=
  (MulEquiv.symm_apply_eq (octonionToChevalley K)).mpr (octonionToChevalley_Y K i t).symm

end Atlas.Chevalley.Comparison.G2
