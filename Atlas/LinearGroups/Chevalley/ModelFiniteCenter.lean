import Atlas.LinearGroups.Chevalley.AdjointFiniteCenter
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! Uniform centerlessness of the actual adjoint models, including the
small nonsimple parameters. No perfectness or simplicity is used. -/
noncomputable section
namespace Atlas.Chevalley

theorem model_center_eq_bot_finiteField
    (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    Subgroup.center (Model Φ K) = ⊥ :=
  adjoint_center_eq_bot_finiteField (rootDatum Φ).pairing (rootDatum Φ).base K
    (rootDatum_simpleDiamondProducts Φ)

end Atlas.Chevalley
