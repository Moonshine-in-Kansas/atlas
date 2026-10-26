import Atlas.GroupTheory.ScalingCommutator
import Atlas.LinearGroups.Chevalley.TorusConjugation
import Atlas.LinearGroups.Chevalley.Models
import Mathlib.GroupTheory.IsPerfect

/-! Actual adjoint perfectness from explicit torus commutators.
No order, simplicity, irreducibility, or old-family result is used. -/
noncomputable section
namespace Atlas.Chevalley
open Group
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (K : Type*) [Field K]

/-- The actual root parameter, packaged as a homomorphism from addition. -/
def adjointXHom (i : b.support) : Multiplicative K →* Adjoint P b K where
  toFun t := adjointX P b K i t.toAdd
  map_one' := by
    have h : adjointX P b K i 0 * adjointX P b K i 0 = adjointX P b K i 0 := by
      simpa using (adjointX_add P b K i 0 0).symm
    exact mul_eq_left.mp h
  map_mul' s t := adjointX_add P b K i s.toAdd t.toAdd

def adjointYHom (i : b.support) : Multiplicative K →* Adjoint P b K where
  toFun t := adjointY P b K i t.toAdd
  map_one' := by
    have h : adjointY P b K i 0 * adjointY P b K i 0 = adjointY P b K i 0 := by
      simpa using (adjointY_add P b K i 0 0).symm
    exact mul_eq_left.mp h
  map_mul' s t := adjointY_add P b K i s.toAdd t.toAdd

theorem adjointX_mem_commutator_of_unit (a : Kˣ) (ha : (a : K)^2 ≠ 1)
    (i : b.support) (t : K) : adjointX P b K i t ∈ commutator (Adjoint P b K) := by
  apply Atlas.GroupTheory.scaled_root_mem_commutator (adjointXHom P b K i)
    (adjointTorus P b K i a) ((a : K)^2) ha
  intro u
  simpa only [adjointXHom, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, b.cartanMatrix_apply_same, zpow_ofNat, Units.val_pow_eq_pow_val]
    using adjointTorus_conjugate_X P b K i i a u

theorem adjointY_mem_commutator_of_unit (a : Kˣ) (ha : (a : K)^2 ≠ 1)
    (i : b.support) (t : K) : adjointY P b K i t ∈ commutator (Adjoint P b K) := by
  apply Atlas.GroupTheory.scaled_root_mem_commutator (adjointYHom P b K i)
    (adjointTorus P b K i a⁻¹) ((a : K)^2) ha
  intro u
  simpa only [adjointYHom, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, b.cartanMatrix_apply_same, zpow_neg, zpow_ofNat,
    inv_pow, inv_inv, Units.val_pow_eq_pow_val]
    using adjointTorus_conjugate_Y P b K i i a⁻¹ u

/-- Every generator is an explicit commutator with an actual torus word. -/
theorem adjoint_isPerfect_of_unit (a : Kˣ) (ha : (a : K)^2 ≠ 1) :
    IsPerfect (Adjoint P b K) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  exact adjoint_induction P b K
    (adjointX_mem_commutator_of_unit P b K a ha)
    (adjointY_mem_commutator_of_unit P b K a ha)
    (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem)
    (fun _ => (commutator _).inv_mem) g

/-- Uniform finite-field result; the two small fields remain separate obligations. -/
theorem adjoint_isPerfect_of_card_gt_three [Fintype K] (hq : 3 < Fintype.card K) :
    IsPerfect (Adjoint P b K) := by
  obtain ⟨a,ha0,ha⟩ := Atlas.GroupTheory.exists_nonzero_sq_ne_one hq
  exact adjoint_isPerfect_of_unit P b K (Units.mk0 a ha0) ha

end Atlas.Chevalley

namespace Atlas.Chevalley
open Group
variable (K : Type*) [Field K]

/-- Actual all-nine adjoint dispatcher, with the same field-size restriction. -/
theorem model_isPerfect_of_card_gt_three (Φ : RootType) [Fintype K]
    (hq : 3 < Fintype.card K) : IsPerfect (Model Φ K) :=
  adjoint_isPerfect_of_card_gt_three (rootDatum Φ).pairing (rootDatum Φ).base K hq

end Atlas.Chevalley
