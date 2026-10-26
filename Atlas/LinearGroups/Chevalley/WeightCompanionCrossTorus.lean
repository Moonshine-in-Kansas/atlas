import Atlas.LinearGroups.Chevalley.WeightCompanionPerfectness
import Atlas.LinearGroups.Chevalley.Integral.MinusculeCrossTorus
import Atlas.LinearGroups.Chevalley.ModelPerfectnessOdd
/-! Actual cross-torus identities and companion
perfectness in odd characteristic when literal Cartan rows have odd entries.
No central-kernel premise; C and B2 remain outside this row criterion. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Group Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

theorem weightCompanionTorus_mul_X_cross (i j : b.support) (a : Rˣ) (s : R) :
    weightCompanionTorus P b O hclosed hmin R j a * weightCompanionX P b O hclosed hmin R i s =
      weightCompanionX P b O hclosed hmin R i ((a ^ b.cartanMatrix i j).val*s) *
        weightCompanionTorus P b O hclosed hmin R j a := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [Subgroup.coe_mul, Prod.fst_mul, weightCompanionTorus_adjoint]
    simpa only [weightCompanionX, weightCompanionRootX] using adjointTorus_mul_X P b R j i a s
  · funext k
    simp only [Subgroup.coe_mul, Prod.snd_mul, Pi.mul_apply, weightCompanionTorus_minuscule]
    simpa only [weightCompanionX, weightCompanionY, weightCompanionRootX, weightCompanionRootY, weightOrbitRootElement, RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn, Matrix.of_apply, neg_neg, one_mul] using
      weightOrbit_torusMatrixUnit_mul_root P (O k) (hclosed k) (hmin k) R i.val j.val (-1) (by decide) a s

theorem weightCompanionTorus_mul_Y_cross (i j : b.support) (a : Rˣ) (s : R) :
    weightCompanionTorus P b O hclosed hmin R j a * weightCompanionY P b O hclosed hmin R i s =
      weightCompanionY P b O hclosed hmin R i ((a ^ (-b.cartanMatrix i j)).val*s) *
        weightCompanionTorus P b O hclosed hmin R j a := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [Subgroup.coe_mul, Prod.fst_mul, weightCompanionTorus_adjoint]
    simpa only [weightCompanionY, weightCompanionRootY] using adjointTorus_mul_Y P b R j i a s
  · funext k
    simp only [Subgroup.coe_mul, Prod.snd_mul, Pi.mul_apply, weightCompanionTorus_minuscule]
    simpa only [weightCompanionX, weightCompanionY, weightCompanionRootX, weightCompanionRootY, weightOrbitRootElement, RootPairing.Base.cartanMatrix, RootPairing.Base.cartanMatrixIn, Matrix.of_apply, neg_one_mul] using
      weightOrbit_torusMatrixUnit_mul_root P (O k) (hclosed k) (hmin k) R i.val j.val 1 (by decide) a s

theorem weightCompanionTorus_conjugate_X_cross (i j : b.support) (a : Rˣ) (s : R) :
    weightCompanionTorus P b O hclosed hmin R j a * weightCompanionX P b O hclosed hmin R i s *
      (weightCompanionTorus P b O hclosed hmin R j a)⁻¹ =
        weightCompanionX P b O hclosed hmin R i ((a ^ b.cartanMatrix i j).val*s) := by
  rw [weightCompanionTorus_mul_X_cross, mul_assoc, mul_inv_cancel, mul_one]

theorem weightCompanionTorus_conjugate_Y_cross (i j : b.support) (a : Rˣ) (s : R) :
    weightCompanionTorus P b O hclosed hmin R j a * weightCompanionY P b O hclosed hmin R i s *
      (weightCompanionTorus P b O hclosed hmin R j a)⁻¹ =
        weightCompanionY P b O hclosed hmin R i ((a ^ (-b.cartanMatrix i j)).val*s) := by
  rw [weightCompanionTorus_mul_Y_cross, mul_assoc, mul_inv_cancel, mul_one]

variable (K : Type*) [Field K]

theorem weightCompanionX_mem_commutator_of_odd_cartan (hchar : (-1 : K) ≠ 1)
    (i j : b.support) (hodd : Odd (b.cartanMatrix i j)) (t : K) :
    weightCompanionX P b O hclosed hmin K i t ∈ commutator (WeightCompanion P b O hclosed hmin K) := by
  let a : Kˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  apply Atlas.GroupTheory.scaled_root_mem_commutator (weightCompanionXHom P b O hclosed hmin K i)
    (weightCompanionTorus P b O hclosed hmin K j a) (-1) hchar
  intro s
  simpa only [weightCompanionXHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    a, Units.val_zpow_eq_zpow_val, Units.val_mk0, hodd.neg_one_zpow] using
      weightCompanionTorus_conjugate_X_cross P b O hclosed hmin K i j a s

theorem weightCompanionY_mem_commutator_of_odd_cartan (hchar : (-1 : K) ≠ 1)
    (i j : b.support) (hodd : Odd (b.cartanMatrix i j)) (t : K) :
    weightCompanionY P b O hclosed hmin K i t ∈ commutator (WeightCompanion P b O hclosed hmin K) := by
  let a : Kˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  apply Atlas.GroupTheory.scaled_root_mem_commutator (weightCompanionYHom P b O hclosed hmin K i)
    (weightCompanionTorus P b O hclosed hmin K j a) (-1) hchar
  intro s
  simpa only [weightCompanionYHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    a, Units.val_zpow_eq_zpow_val, Units.val_mk0, hodd.neg.neg_one_zpow] using
      weightCompanionTorus_conjugate_Y_cross P b O hclosed hmin K i j a s

theorem weightCompanion_isPerfect_of_odd_cartan_rows (hchar : (-1 : K) ≠ 1)
    (hrows : ∀ i : b.support, ∃ j : b.support, Odd (b.cartanMatrix i j)) :
    IsPerfect (WeightCompanion P b O hclosed hmin K) := by
  apply isPerfect_def.mpr
  apply top_unique
  intro g hg
  apply weightCompanion_induction P b O hclosed hmin K ?_ ?_ (commutator _).one_mem
    (fun _ _ => (commutator _).mul_mem) (fun _ => (commutator _).inv_mem) g
  · intro i t
    obtain ⟨j,hj⟩ := hrows i
    exact weightCompanionX_mem_commutator_of_odd_cartan P b O hclosed hmin K hchar i j hj t
  · intro i t
    obtain ⟨j,hj⟩ := hrows i
    exact weightCompanionY_mem_commutator_of_odd_cartan P b O hclosed hmin K hchar i j hj t

theorem weightCompanion_isPerfect_of_card_three [Fintype K] (hq : Fintype.card K = 3)
    (hrows : ∀ i : b.support, ∃ j : b.support, Odd (b.cartanMatrix i j)) :
    IsPerfect (WeightCompanion P b O hclosed hmin K) :=
  weightCompanion_isPerfect_of_odd_cartan_rows P b O hclosed hmin K
    (neg_one_ne_one_of_card_three K hq) hrows
end Atlas.Chevalley
