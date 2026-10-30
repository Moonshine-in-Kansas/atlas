import Atlas.LinearGroups.Chevalley.Comparison.F4.AlbertLift
import Atlas.LinearGroups.Chevalley.ModelF4Order
import Atlas.LinearGroups.F4.Order

/-! Actual marked equivalence of the Chevalley and full Albert models.
The map is constructed from root actions before the two independent finite
orders identify its domain and kernel. No simplicity or recognition is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Atlas.LinearAlgebra
variable (K : Type*) [Field K] [Finite K]

theorem independent_orders_equal :
    Nat.card (Atlas.F4.Model K) = Nat.card (Model .F4 K) := by
  rw [Atlas.F4.card_Model, model_F4_card]
  ring

theorem albertLiftSubgroup_eq_top : albertLiftSubgroup K = ⊤ :=
  (Atlas.GroupTheory.subgroup_eq_top_and_bijective_of_surjective_of_card
    (albertLiftSubgroup K) (albertLiftHom K) (albertLiftHom_surjective K)
    (independent_orders_equal K)).1

def albertToChevalley : Atlas.F4.Model K ≃* Model .F4 K :=
  faithfulConjugationLiftEquiv (albertMatrixHom K) (matrixEmbedding K) (geckRepresentation K)
    (matrixEmbedding_injective K) (geckRepresentation_injective K)
    (albertLiftHom_surjective K) (independent_orders_equal K)

def albertEquiv : Model .F4 K ≃* Atlas.F4.Model K := (albertToChevalley K).symm

theorem albertToChevalley_X (i : Fin 4) (t : K) :
    albertToChevalley K (albertSimple (F:=K) (Fin.castAdd 4 i) t) =
      modelX .F4 K i t :=
  faithfulConjugationLiftEquiv_eq (albertMatrixHom K) (matrixEmbedding K) (geckRepresentation K)
    (matrixEmbedding_injective K) (geckRepresentation_injective K)
    (albertLiftHom_surjective K) (independent_orders_equal K) _ _
    (albert_X_compatible K i t)

theorem albertToChevalley_Y (i : Fin 4) (t : K) :
    albertToChevalley K (albertSimple (F:=K) (Fin.natAdd 4 i) t) =
      modelY .F4 K i t :=
  faithfulConjugationLiftEquiv_eq (albertMatrixHom K) (matrixEmbedding K) (geckRepresentation K)
    (matrixEmbedding_injective K) (geckRepresentation_injective K)
    (albertLiftHom_surjective K) (independent_orders_equal K) _ _
    (albert_Y_compatible K i t)

theorem albertEquiv_X (i : Fin 4) (t : K) :
    albertEquiv K (modelX .F4 K i t) =
      albertSimple (F:=K) (Fin.castAdd 4 i) t :=
  (MulEquiv.symm_apply_eq (albertToChevalley K)).mpr (albertToChevalley_X K i t).symm

theorem albertEquiv_Y (i : Fin 4) (t : K) :
    albertEquiv K (modelY .F4 K i t) =
      albertSimple (F:=K) (Fin.natAdd 4 i) t :=
  (MulEquiv.symm_apply_eq (albertToChevalley K)).mpr (albertToChevalley_Y K i t).symm

/-- The comparison preserves the pre-existing positive root parameters. -/
theorem albertEquiv_simplePositive (i : Fin 4) (t : K) :
    albertEquiv K (modelX .F4 K i t) = Atlas.F4.simplePositive i t := by
  simpa only [albertSimple, Fin.addCases_left] using albertEquiv_X K i t

/-- The minus sign records the Wilson negative-root convention explicitly. -/
theorem albertEquiv_simpleNegative (i : Fin 4) (t : K) :
    albertEquiv K (modelY .F4 K i t) = Atlas.F4.simpleNegative i (-t) := by
  simpa only [albertSimple, Fin.addCases_right] using albertEquiv_Y K i t

end Atlas.Chevalley.Comparison.F4
