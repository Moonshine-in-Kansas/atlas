import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2WeylCorrespondence

/-! Actual same-root Weyl conjugation for the long
C2 root. Integer coefficient identities precede arbitrary-ring base change.
This fills a missing interface: the earlier Weyl vector-action theorems do
not themselves state conjugation of whole root elements. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData C2IntegerTemplate
open scoped Matrix
local instance c2LoweringRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance c2LoweringBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The first divided coefficient changes sign under the actual Weyl word. -/
theorem c2_nb_eb_nbInv : nb * eb * nbInv = -(omega * eb * omega) := by decide

/-- The second divided coefficient keeps its sign, including in characteristic two. -/
theorem c2_nb_eb2_nbInv : nb * eb2 * nbInv = omega * eb2 * omega := by decide

variable {R : Type*} [CommRing R]

theorem c2_omegaOver_sq :
    omega.map (Int.castRingHom R) * omega.map (Int.castRingHom R) =
      (1 : Matrix (Fin 10) (Fin 10) R) := by
  have h := congrArg (c2Reindex R)
    (oppositionOver_mul_self (pairingC 2) (baseC 1) R)
  simpa only [map_mul, map_one, c2_reindex_opposition] using h

theorem c2_weyl_conjugate_xbOver (t : R) :
    (Int.castRingHom R).mapMatrix nb * xbOver t *
      (Int.castRingHom R).mapMatrix nbInv = ybOver (-t) := by
  let c := (Int.castRingHom R).mapMatrix (m := Fin 10)
  have h0 : c nb * c nbInv = 1 := by rw [← map_mul, nb_mul_nbInv, map_one]
  have h1 : c nb * c eb * c nbInv = -(c omega * c eb * c omega) := by
    rw [← map_mul, ← map_mul, c2_nb_eb_nbInv, map_neg, map_mul, map_mul]
  have h2 : c nb * c eb2 * c nbInv = c omega * c eb2 * c omega := by
    rw [← map_mul, ← map_mul, c2_nb_eb2_nbInv, map_mul, map_mul]
  have ho : c omega * c omega = 1 := c2_omegaOver_sq
  change c nb * (1 + t • c eb + t^2 • c eb2) * c nbInv =
    c omega * (1 + (-t) • c eb + (-t)^2 • c eb2) * c omega
  simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc]
  rw [h0, h1, h2, ho]
  simp only [smul_neg, neg_smul, neg_sq]

/-- Conjugation holds in the previously defined adjoint group itself. -/
theorem c2_weyl_long_conjugate_X (t : R) :
    adjointWeyl (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) 1 *
      adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) t *
      (adjointWeyl (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) 1)⁻¹ =
      adjointY (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) (-t) := by
  apply c2AdjointMatrixHom_injective R
  rw [map_mul, map_mul, c2_matrix_weyl_long, c2_matrix_xlong,
    c2_matrix_weyl_long_inv, c2_matrix_ylong]
  exact c2_weyl_conjugate_xbOver t

end Atlas.Chevalley.Integral.RankTwo
