import Atlas.LinearGroups.ReeF4.RootGroupMembership
import Atlas.LinearGroups.ReeF4.WeylModel
import Atlas.LinearGroups.ReeF4.SpecialVectors

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Triangular parameters for the actual C4,B4,B3,C3 natural Suzuki block. -/
def secondPivotA (w : TraceZero F) : F := w.val.2 1 7 / w.val.2 2 7

def secondPivotB (m : ℕ) (w : TraceZero F) : F :=
  (w.val.2 1 6 + theta F m (secondPivotA w)*w.val.2 1 7) / w.val.2 2 7

def secondPivot {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (w : TraceZero F) : Model F m :=
  ⟨shortRootPairEquiv m hcard (secondPivotA w) (secondPivotB m w),
    shortRootPairEquiv_mem_modelSubgroup hcard _ _⟩

theorem secondPivot_preserves_A4 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : TraceZero F) :
    ((secondPivot hcard w).val w).val.2 0 7 = w.val.2 0 7 := rfl

theorem secondPivot_preserves_C4 {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : TraceZero F) :
    ((secondPivot hcard w).val w).val.2 2 7 = w.val.2 2 7 := rfl

theorem secondPivot_B4_zero {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : TraceZero F)
    (hc : w.val.2 2 7 ≠ 0) : ((secondPivot hcard w).val w).val.2 1 7 = 0 := by
  change w.val.2 1 7 + (w.val.2 1 7 / w.val.2 2 7)*w.val.2 2 7 = 0
  rw [div_mul_cancel₀ _ hc,CharTwo.add_self_eq_zero]

theorem secondPivot_B3_zero {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : TraceZero F)
    (hc : w.val.2 2 7 ≠ 0) : ((secondPivot hcard w).val w).val.2 1 6 = 0 := by
  change (w.val.2 1 6 + secondPivotB m w*w.val.2 2 7) +
    theta F m (secondPivotA w)*w.val.2 1 7 = 0
  unfold secondPivotB
  rw [div_mul_cancel₀ _ hc]
  linear_combination (w.val.2 1 6 + theta F m (secondPivotA w)*w.val.2 1 7)*
    (CharTwo.two_eq_zero (R := F))

/-- The exact remaining obstruction; no assertion that it vanishes is hidden. -/
theorem secondPivot_C3_residual {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (w : TraceZero F)
    (hc : w.val.2 2 7 ≠ 0) :
    ((secondPivot hcard w).val w).val.2 2 6 =
      w.val.2 2 6 + w.val.2 2 7 *
        (theta F m (secondPivotB m w) + secondPivotA w * secondPivotB m w +
          secondPivotA w ^ 2 * theta F m (secondPivotA w)) := by
  have ha : secondPivotA w * w.val.2 2 7 = w.val.2 1 7 :=
    div_mul_cancel₀ _ hc
  have hb : secondPivotB m w * w.val.2 2 7 =
      w.val.2 1 6 + theta F m (secondPivotA w)*w.val.2 1 7 :=
    div_mul_cancel₀ _ hc
  change (w.val.2 2 6 + secondPivotB m w*w.val.2 1 7 +
      theta F m (secondPivotB m w)*w.val.2 2 7) +
      secondPivotA w*(w.val.2 1 6 + secondPivotB m w*w.val.2 2 7) +
      secondPivotA w*theta F m (secondPivotA w)*w.val.2 1 7 +
      secondPivotA w^2*(theta F m (secondPivotA w))*w.val.2 2 7 = _
  rw [hb]
  linear_combination -(secondPivotB m w) * ha +
    (secondPivotA w*w.val.2 1 6 +
      secondPivotA w*theta F m (secondPivotA w)*w.val.2 1 7)*
      (CharTwo.two_eq_zero (R := F))

theorem secondPivot_special {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {w : TraceZero F}
    (hw : IsSpecialVector m w) : IsSpecialVector m ((secondPivot hcard w).val w) :=
  hw.map_model (secondPivot hcard w)

end Atlas.ReeF4
