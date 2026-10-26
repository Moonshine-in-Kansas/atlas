import Atlas.LinearGroups.Chevalley.Comparison.TypeASpecialLinearSurjective
import Atlas.LinearGroups.Chevalley.ModelAOrder

/-! A comparison of two already defined models. The literal surjective
weight-block homomorphism is bijective by their independently proved orders.
The new uniform order proof does not depend on this comparison. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeA
open scoped MatrixGroups

theorem companion_card_eq_SL (r : ℕ) (hr : 1 ≤ r)
    (K : Type*) [Field K] [Finite K] :
    Nat.card (SelectedWeightCompanion (.A r hr) K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin (r + 1)) K) := by
  classical
  have hsl : Nat.card (Matrix.SpecialLinearGroup (Fin (r + 1)) K) =
      Nat.card (PGL(r + 1, K)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) K))]
    change Nat.card (PSL(r + 1, K)) *
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin (r + 1)) K)) = _
    rw [Atlas.card_sl_center]
    exact Atlas.card_psl_mul_pgl
  rw [selectedWeightCompanion_A_card, hsl, Atlas.card_pgl_factor]
  congr 1
  · congr 1
    simp [Nat.mul_comm]
  · rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
    have he : r + 1 + 1 - 2 = r := by omega
    simp only [he]
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    omega

def specialLinearEquiv (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] [Finite K] :
    SelectedWeightCompanion (.A r hr) K ≃*
      Matrix.SpecialLinearGroup (Fin (r + 1)) K :=
  MulEquiv.ofBijective (specialLinearHom r hr K)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨specialLinearHom_surjective r hr K, companion_card_eq_SL r hr K⟩)

theorem specialLinearEquiv_X (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] [Finite K]
    (i : Fin r) (t : K) :
    specialLinearEquiv r hr K (selectedWeightCompanionX (.A r hr) K i t) =
      Matrix.SpecialLinearGroup.transvection (adjacent_ne i) t :=
  specialLinearHom_X r hr K i t

theorem specialLinearEquiv_Y (r : ℕ) (hr : 1 ≤ r) (K : Type*) [Field K] [Finite K]
    (i : Fin r) (t : K) :
    specialLinearEquiv r hr K (selectedWeightCompanionY (.A r hr) K i t) =
      Matrix.SpecialLinearGroup.transvection (adjacent_ne i).symm t :=
  specialLinearHom_Y r hr K i t

end Atlas.Chevalley.Comparison.TypeA
