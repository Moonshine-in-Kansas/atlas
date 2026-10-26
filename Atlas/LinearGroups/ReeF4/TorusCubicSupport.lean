import Atlas.LinearGroups.ReeF4.TorusQuadratic

/-! The 32 monomials of the retained octonion triple trace in characteristic
 two. Their torus character sums vanish as integer identities, independently
 of the finite-field twist relation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def cubicTripleIndices : Fin 32 → Fin 8 × Fin 8 × Fin 8 :=
  ![(0,4,7), (1,2,7), (2,1,7), (3,0,7),
    (0,7,3), (3,3,3), (5,2,3), (6,1,3),
    (1,7,2), (3,5,2), (5,4,2), (7,1,2),
    (2,7,1), (3,6,1), (6,4,1), (7,2,1),
    (0,5,6), (1,3,6), (4,1,6), (5,0,6),
    (0,6,5), (2,3,5), (4,2,5), (6,0,5),
    (1,6,4), (2,5,4), (4,4,4), (7,0,4),
    (4,7,0), (5,6,0), (6,5,0), (7,3,0)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem octonionTripleTrace_eq_sum (x y z : SplitOctonion.Carrier F) :
    SplitOctonion.trace (SplitOctonion.mul (SplitOctonion.mul x y) z) =
      ∑ i : Fin 32, x (cubicTripleIndices i).1 * y (cubicTripleIndices i).2.1 *
        z (cubicTripleIndices i).2.2 := by
  simp [SplitOctonion.trace, SplitOctonion.mul, cubicTripleIndices,
    Fin.sum_univ_succ, sub_eq_add_neg, CharTwo.neg_eq]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem cubicTripleExponents (m : ℕ) (i : Fin 32) :
    torusWeightExponents m (0,(cubicTripleIndices i).1) +
      torusWeightExponents m (1,(cubicTripleIndices i).2.1) +
      torusWeightExponents m (2,(cubicTripleIndices i).2.2) = 0 := by
  fin_cases i <;> ext <;> simp [cubicTripleIndices, torusWeightExponents] <;> ring

variable {G : Type*} [CommGroup G]

theorem torusCubicTriple_weight (m : ℕ) (a b : G) (i : Fin 32) :
    torusWeight m a b (0,(cubicTripleIndices i).1) *
      torusWeight m a b (1,(cubicTripleIndices i).2.1) *
      torusWeight m a b (2,(cubicTripleIndices i).2.2) = 1 := by
  have h1 := congrArg Prod.fst (cubicTripleExponents m i)
  have h2 := congrArg Prod.snd (cubicTripleExponents m i)
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] at h1 h2
  calc
    _ = a ^ ((torusWeightExponents m (0,(cubicTripleIndices i).1)).1 +
          (torusWeightExponents m (1,(cubicTripleIndices i).2.1)).1 +
          (torusWeightExponents m (2,(cubicTripleIndices i).2.2)).1) *
        b ^ ((torusWeightExponents m (0,(cubicTripleIndices i).1)).2 +
          (torusWeightExponents m (1,(cubicTripleIndices i).2.1)).2 +
          (torusWeightExponents m (2,(cubicTripleIndices i).2.2)).2) := by
      simp only [torusWeight, zpow_add]
      ac_rfl
    _ = 1 := by rw [h1, h2]; simp

end Atlas.ReeF4
