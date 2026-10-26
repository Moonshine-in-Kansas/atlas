import Atlas.LinearGroups.Chevalley.RootData.RootStringReflectionTransport
import Atlas.LinearGroups.Chevalley.WeylRootActionComplete
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! Source candidate: the literal A2 braid on every Geck basis column.
No root-subgroup commutator, irreducibility or projection injectivity is assumed. -/

noncomputable section
open scoped Matrix
namespace Atlas.Chevalley
open Integral
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

private theorem a2_chain_outer (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (k : ι) :
    P.chainBotCoeff i (P.reflectionPerm j (P.reflectionPerm i k)) =
      P.chainBotCoeff j k := by
  have hs := RootData.a2_reflected_simple_labels P b i j hij hji
  have hl : P.reflectionPerm i (P.reflectionPerm j i) = j := by
    rw [← hs, P.reflectionPerm_self]
  rw [RootData.chainBotCoeff_reflection_right,
    RootData.chainBotCoeff_reflection_right, hl]

private theorem a2_chain_middle (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (k : ι) :
    P.chainBotCoeff j (P.reflectionPerm i k) =
      P.chainBotCoeff i (P.reflectionPerm j k) := by
  rw [RootData.chainBotCoeff_reflection_right, RootData.chainBotCoeff_reflection_right,
    RootData.a2_reflected_simple_labels P b i j hij hji]

theorem adjointWeyl_a2_braid_root (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (k : ι) :
    ((adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val) *ᵥ rootVector P b R k =
    ((adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
      (adjointWeyl P b R j 1).val.val) *ᵥ rootVector P b R k := by
  have hl := congrArg (fun w : Equiv.Perm ι => w k)
    (RootData.reflectionPerm_a2_braid P b i j hij hji)
  simp only [Equiv.Perm.mul_apply] at hl
  simp only [← Matrix.mulVec_mulVec, adjointWeyl_one_root_signed,
    Matrix.mulVec_smul, smul_smul,
    a2_chain_outer P b i j hij hji k, a2_chain_outer P b j i hji hij k,
    a2_chain_middle P b i j hij hji k, hl]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem adjointWeyl_a2_braid_cartan (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) (k : b.support) :
    ((adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val) *ᵥ cartanVector P b R k =
    ((adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
      (adjointWeyl P b R j 1).val.val) *ᵥ cartanVector P b R k := by
  simp only [← Matrix.mulVec_mulVec, adjointWeyl_cartan,
    Matrix.mulVec_sub, Matrix.mulVec_smul, b.cartanMatrix_apply_same, hij, hji]
  norm_num <;> module

/-- Equality in the actual adjoint subgroup, proved on all coordinate columns. -/
theorem adjointWeyl_a2_braid (i j : b.support)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -1) :
    adjointWeyl P b R i 1 * adjointWeyl P b R j 1 * adjointWeyl P b R i 1 =
      adjointWeyl P b R j 1 * adjointWeyl P b R i 1 * adjointWeyl P b R j 1 := by
  have hv (k : ι) : rootVector P b R k = Pi.single (Sum.inr k) 1 := by
    ext row
    by_cases h : row = Sum.inr k <;>
      simp [rootVector, RootPairing.GeckConstruction.v, Function.comp_def, Pi.single_apply, h]
  have hu (k : b.support) : cartanVector P b R k = Pi.single (Sum.inl k) 1 := by
    ext row
    by_cases h : row = Sum.inl k <;>
      simp [cartanVector, RootPairing.GeckConstruction.u, Function.comp_def, Pi.single_apply, h]
  apply Subtype.ext
  apply Units.ext
  change (adjointWeyl P b R i 1).val.val * (adjointWeyl P b R j 1).val.val *
      (adjointWeyl P b R i 1).val.val =
    (adjointWeyl P b R j 1).val.val * (adjointWeyl P b R i 1).val.val *
      (adjointWeyl P b R j 1).val.val
  apply Matrix.ext_of_mulVec_single
  intro k
  cases k with
  | inl k =>
    rw [← hu k]
    exact adjointWeyl_a2_braid_cartan P b R i j hij hji k
  | inr k =>
    rw [← hv k]
    exact adjointWeyl_a2_braid_root P b R i j hij hji k

end Atlas.Chevalley
