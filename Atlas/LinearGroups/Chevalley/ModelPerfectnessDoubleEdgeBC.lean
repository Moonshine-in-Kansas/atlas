import Atlas.LinearGroups.Chevalley.AdjointPerfectnessDoubleEdge
import Atlas.LinearGroups.Chevalley.RootData.DoubleEdgeCoverBC
import Atlas.LinearGroups.Chevalley.ModelOppositeSimple

/-! Uncompiled source candidate. All-ring perfectness of the actual
uniform B/C adjoint models in rank at least three, using single-edge
commutators and division-free propagation over the terminal double edge. -/

noncomputable section
namespace Atlas.Chevalley
open Group

/-- The uniform type-B adjoint model is perfect over every commutative
ring in rank at least three, including characteristic two and three. -/
theorem model_B_isPerfect_of_rank_ge_three (r : ℕ) (hr : 3 ≤ r)
    (R : Type*) [CommRing R] :
    IsPerfect (Model (.B r (by omega)) R) := by
  apply adjoint_isPerfect_of_a2_double_cover
    (rootDatum (.B r (by omega))).pairing (rootDatum (.B r (by omega))).base
    (rootDatum_simpleDiamondProducts (.B r (by omega))) R
  with_unfolding_all exact B_base_a2_double_cover (r - 1) (by omega)

/-- The uniform type-C adjoint model is perfect over every commutative
ring in rank at least three, including characteristic two and three. -/
theorem model_C_isPerfect_of_rank_ge_three (r : ℕ) (hr : 3 ≤ r)
    (R : Type*) [CommRing R] :
    IsPerfect (Model (.C r (by omega)) R) := by
  apply adjoint_isPerfect_of_a2_double_cover
    (rootDatum (.C r (by omega))).pairing (rootDatum (.C r (by omega))).base
    (rootDatum_simpleDiamondProducts (.C r (by omega))) R
  with_unfolding_all exact C_base_a2_double_cover (r - 1) (by omega)

end Atlas.Chevalley
