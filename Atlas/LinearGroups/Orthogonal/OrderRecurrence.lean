import Atlas.LinearGroups.Orthogonal.PairOrbit
import Atlas.LinearGroups.Orthogonal.IsometryTransport
import Atlas.LinearGroups.Orthogonal.StandardComplement
import Atlas.LinearGroups.Orthogonal.PairCount

/-! # Full orthogonal group order recurrences in every finite characteristic -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F]

def standardPairD : hyperbolicPairs (formD (n+1) F) :=
  ⟨(e 0, f 0), formD_e 0, formD_f 0, polarD_ef 0⟩

def standardPairB : hyperbolicPairs (formB (n+1) F) :=
  ⟨((e 0, 0), (f 0, 0)), by simp only [formB_apply, formD_e, zero_pow (by decide : 2 ≠ 0), add_zero], by simp only [formB_apply, formD_f, zero_pow (by decide : 2 ≠ 0), add_zero],
    by simp only [polarB_apply, polarD_ef, mul_zero, add_zero]⟩

/-- Full standard-pair stabilizer in split D is the lower-rank full orthogonal group. -/
def standardPairStabilizerD : pairStabilizer (formD (n+1) F) (e 0) (f 0) ≃* O_DPlus n F :=
  (pairStabilizerEquiv _ _ _ (formD_e 0) (formD_f 0) (polarD_ef 0)).trans
    (isometryGroupTransport standardComplementD)

/-- Full standard-pair stabilizer in B, retaining its final quadratic coordinate. -/
def standardPairStabilizerB : pairStabilizer (formB (n+1) F) (e 0, 0) (f 0, 0) ≃* O_B n F :=
  (pairStabilizerEquiv _ _ _ (standardPairB (n := n) (F := F)).prop.1
    (standardPairB (n := n) (F := F)).prop.2.1 (standardPairB (n := n) (F := F)).prop.2.2).trans
    (isometryGroupTransport standardComplementB)

variable [Finite F]

theorem card_fullB_succ : Nat.card (O_B (n+1) F) =
    ((Nat.card F ^ (2*(n+1)) - 1) * Nat.card F ^ (2*(n+1)-1)) * Nat.card (O_B n F) := by
  have h := card_isometry_eq_pairs_mul_complement (formB (n+1) F) radicalB_eq_bot
    (standardPairB (n := n) (F := F))
  have hc := Nat.card_congr (isometryGroupTransport (standardComplementB (n := n) (F := F))).toEquiv
  change Nat.card (O_B (n+1) F) = Nat.card (HyperbolicPairsB (n+1) F) *
    Nat.card (isometrySubgroup (Atlas.Quadratic.complementForm (formB (n+1) F) (e 0, 0) (f 0, 0))) at h
  rw [hc, card_hyperbolicPairsB] at h
  exact h

theorem card_fullD_succ : Nat.card (O_DPlus (n+1) F) =
    ((Nat.card F ^ (n+1)-1) * (Nat.card F ^ n+1) * Nat.card F ^ (2*n)) *
      Nat.card (O_DPlus n F) := by
  have h := card_isometry_eq_pairs_mul_complement (formD (n+1) F) radicalD_eq_bot
    (standardPairD (n := n) (F := F))
  have hc := Nat.card_congr (isometryGroupTransport (standardComplementD (n := n) (F := F))).toEquiv
  change Nat.card (O_DPlus (n+1) F) = Nat.card (HyperbolicPairsD (n+1) F) *
    Nat.card (isometrySubgroup (Atlas.Quadratic.complementForm (formD (n+1) F) (e 0) (f 0))) at h
  rw [hc, card_hyperbolicPairsD] at h
  convert h using 1 <;> congr 2 <;> omega

end Atlas.Orthogonal
