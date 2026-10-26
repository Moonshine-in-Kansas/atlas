import Atlas.LinearGroups.Chevalley.WeightCompanionRootLaws
import Atlas.LinearGroups.Chevalley.Integral.MinusculeTorusConjugation

/-! Actual simultaneous torus words, coordinate identities, and same-root conjugation. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

def weightCompanionWeyl (i : b.support) (t : Rˣ) : WeightCompanion P b O hclosed hmin R :=
  weightCompanionX P b O hclosed hmin R i t.val *
    weightCompanionY P b O hclosed hmin R i (-t.inv) *
      weightCompanionX P b O hclosed hmin R i t.val

def weightCompanionTorus (i : b.support) (t : Rˣ) : WeightCompanion P b O hclosed hmin R :=
  weightCompanionWeyl P b O hclosed hmin R i t *
    (weightCompanionWeyl P b O hclosed hmin R i 1)⁻¹

/-- The first coordinate is the actual adjoint torus word. -/
theorem weightCompanionTorus_adjoint (i : b.support) (a : Rˣ) :
    (weightCompanionTorus P b O hclosed hmin R i a).val.1 =
      adjointTorus P b R i a := rfl

/-- Every weight coordinate is the literal minuscule matrix torus word. -/
theorem weightCompanionTorus_minuscule (i : b.support) (a : Rˣ) (k : κ) :
    (weightCompanionTorus P b O hclosed hmin R i a).val.2 k =
      (stringsOfWeightOrbit P (O k) (hclosed k) (hmin k)).torusMatrixUnit R i.val a := rfl

theorem weightCompanionRho_torus (i : b.support) (t : Rˣ) :
    weightCompanionRho P b O hclosed hmin R (weightCompanionTorus P b O hclosed hmin R i t) =
      adjointTorus P b R i t := by
  simp only [weightCompanionTorus, weightCompanionWeyl, adjointTorus, adjointWeyl,
    map_mul, map_inv, weightCompanionRho_X, weightCompanionRho_Y]

theorem weightCompanionTorus_mul_X (i : b.support) (a : Rˣ) (s : R) :
    weightCompanionTorus P b O hclosed hmin R i a * weightCompanionX P b O hclosed hmin R i s =
      weightCompanionX P b O hclosed hmin R i (a.val^2*s) * weightCompanionTorus P b O hclosed hmin R i a := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [Subgroup.coe_mul, Prod.fst_mul, weightCompanionTorus_adjoint]
    simpa only [weightCompanionX, weightCompanionRootX, b.cartanMatrix_apply_same, zpow_ofNat, Units.val_pow_eq_pow_val]
      using adjointTorus_mul_X P b R i i a s
  · funext k
    exact (stringsOfWeightOrbit P (O k) (hclosed k) (hmin k)).torusMatrixUnit_mul_raising
      R i.val a s

theorem weightCompanionTorus_mul_Y (i : b.support) (a : Rˣ) (s : R) :
    weightCompanionTorus P b O hclosed hmin R i a * weightCompanionY P b O hclosed hmin R i s =
      weightCompanionY P b O hclosed hmin R i (a.inv^2*s) * weightCompanionTorus P b O hclosed hmin R i a := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [Subgroup.coe_mul, Prod.fst_mul, weightCompanionTorus_adjoint]
    simpa only [weightCompanionY, weightCompanionRootY, b.cartanMatrix_apply_same, zpow_neg, zpow_ofNat, Units.inv_pow_eq_pow_inv, Units.inv_eq_val_inv]
      using adjointTorus_mul_Y P b R i i a s
  · funext k
    exact (stringsOfWeightOrbit P (O k) (hclosed k) (hmin k)).torusMatrixUnit_mul_lowering
      R i.val a s

theorem weightCompanionTorus_conjugate_X (i : b.support) (a : Rˣ) (s : R) :
    weightCompanionTorus P b O hclosed hmin R i a * weightCompanionX P b O hclosed hmin R i s *
      (weightCompanionTorus P b O hclosed hmin R i a)⁻¹ =
        weightCompanionX P b O hclosed hmin R i (a.val^2*s) := by
  rw [weightCompanionTorus_mul_X, mul_assoc, mul_inv_cancel, mul_one]

theorem weightCompanionTorus_conjugate_Y (i : b.support) (a : Rˣ) (s : R) :
    weightCompanionTorus P b O hclosed hmin R i a * weightCompanionY P b O hclosed hmin R i s *
      (weightCompanionTorus P b O hclosed hmin R i a)⁻¹ =
        weightCompanionY P b O hclosed hmin R i (a.inv^2*s) := by
  rw [weightCompanionTorus_mul_Y, mul_assoc, mul_inv_cancel, mul_one]
end Atlas.Chevalley
