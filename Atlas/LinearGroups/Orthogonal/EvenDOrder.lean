import Atlas.LinearGroups.Orthogonal.StableReflectionGenerationD
import Atlas.LinearGroups.Orthogonal.EvenDReflectionIdentification
import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB

/-! # Exact orders of the actual characteristic-two split-D groups

Full reflection generation and the intrinsic residual-parity kernel identify the
actual elementary subgroup as index two. The full orthogonal-group order was
obtained independently by hyperbolic-pair counting. Scalar quotienting changes
nothing in characteristic two. No simplicity statement is used.
-/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- Exact index two for the actual elementary subgroup inside the full split-D group. -/
theorem card_evenElementaryD_mul_two (n : ℕ) :
    Nat.card (elementarySubgroup (formD (n + 3) F)) * 2 = Nat.card (O_DPlus (n + 3) F) := by
  let i : Fin (n + 3) := 0
  have h := card_evenReflection_mul_two (formD (n + 3) F) polarD_nondegenerate
    (e i - f i) (exchange_direction_nonzero _ _ _ (formD_e i) (formD_f i) (polarD_ef i))
  rw [evenReflectionD_eq_elementary, reflectionSubgroupD_eq_top_stable,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at h
  exact h

/-- Uniform elementary split-D order, including the field with two elements. -/
theorem card_evenElementaryD (n : ℕ) :
    Nat.card (elementarySubgroup (formD (n + 3) F)) =
      Nat.card F ^ ((n + 3) * (n + 2)) * (Nat.card F ^ (n + 3) - 1) *
        ∏ i ∈ Finset.range (n + 2), (Nat.card F ^ (2 * (i + 1)) - 1) := by
  have h := card_evenElementaryD_mul_two (F := F) n
  rw [card_fullD (n + 2)] at h
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
  calc
    Nat.card (elementarySubgroup (formD (n + 3) F)) * 2 = _ := h
    _ = _ := by ring

/-- Order of the actual projective elementary model; its scalar kernel is trivial. -/
theorem card_evenProjectiveD (n : ℕ) :
    Nat.card (ProjectiveElementary (formD (n + 3) F)) =
      Nat.card F ^ ((n + 3) * (n + 2)) * (Nat.card F ^ (n + 3) - 1) *
        ∏ i ∈ Finset.range (n + 2), (Nat.card F ^ (2 * (i + 1)) - 1) := by
  rw [Nat.card_congr (evenProjectiveElementaryEquiv _).toEquiv, card_evenElementaryD]

end Atlas.Orthogonal
