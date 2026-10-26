import Atlas.LinearGroups.Chevalley.WeightCompanionCrossTorus
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusParameters

/-! Actual Weyl/torus normalizer identities, before any Bruhat assertion. -/
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


/-- Conjugating the actual three-factor Weyl word rescales its unit parameter. -/
theorem weightCompanionTorus_conjugate_Weyl (i j : b.support) (a t : Rˣ) :
    weightCompanionTorus P b O hclosed hmin R j a *
      weightCompanionWeyl P b O hclosed hmin R i t *
        (weightCompanionTorus P b O hclosed hmin R j a)⁻¹ =
      weightCompanionWeyl P b O hclosed hmin R i (a ^ b.cartanMatrix i j * t) := by
  let T := weightCompanionTorus P b O hclosed hmin R j a
  have hneg : ((a ^ (-b.cartanMatrix i j)).val * (-t.inv)) =
      -(a ^ b.cartanMatrix i j * t).inv := by
    simp [Units.inv_eq_val_inv,mul_inv_rev,zpow_neg,Units.val_mul,mul_comm]
  calc
    _ = (T * weightCompanionX P b O hclosed hmin R i t.val * T⁻¹) *
        (T * weightCompanionY P b O hclosed hmin R i (-t.inv) * T⁻¹) *
        (T * weightCompanionX P b O hclosed hmin R i t.val * T⁻¹) := by
          dsimp [T,weightCompanionWeyl]
          group
    _ = _ := by
      dsimp only [T]
      simp only [weightCompanionTorus_conjugate_X_cross,
        weightCompanionTorus_conjugate_Y_cross,hneg,weightCompanionWeyl,Units.val_mul]

/-- Exact simple-coroot reflection on the actual simultaneous torus.
The exponent uses Cartan row i, column j. -/
theorem weightCompanionWeyl_conjugate_Torus (i j : b.support) (a : Rˣ) :
    weightCompanionWeyl P b O hclosed hmin R i 1 *
      weightCompanionTorus P b O hclosed hmin R j a *
        (weightCompanionWeyl P b O hclosed hmin R i 1)⁻¹ =
      weightCompanionTorus P b O hclosed hmin R i (a ^ (-b.cartanMatrix i j)) *
        weightCompanionTorus P b O hclosed hmin R j a := by
  let W := weightCompanionWeyl P b O hclosed hmin R i 1
  let T := weightCompanionTorus P b O hclosed hmin R j a
  let c := a ^ b.cartanMatrix i j
  let H := weightCompanionTorus P b O hclosed hmin R i c
  have hc : T * W * T⁻¹ = weightCompanionWeyl P b O hclosed hmin R i c := by
    simpa only [mul_one] using weightCompanionTorus_conjugate_Weyl P b O hclosed hmin R i j a 1
  have hstep : T*W=H*W*T := by
    change T*W=(weightCompanionWeyl P b O hclosed hmin R i c * W⁻¹)*W*T
    rw [← hc]
    group
  have hinv : H⁻¹=weightCompanionTorus P b O hclosed hmin R i c⁻¹ := by
    have hp : H * weightCompanionTorus P b O hclosed hmin R i c⁻¹=1 := by
      dsimp only [H]
      rw [← weightCompanionTorus_mul]
      simp [weightCompanionTorus]
    calc
      H⁻¹=H⁻¹*(H*weightCompanionTorus P b O hclosed hmin R i c⁻¹) := by rw [hp,mul_one]
      _ = _ := by group
  change W*T*W⁻¹ = _
  calc
    W*T*W⁻¹ = H⁻¹*(T*W)*W⁻¹ := by rw [hstep]; group
    _ = H⁻¹*T := by group
    _ = _ := by rw [hinv]; simp only [c,zpow_neg]; rfl
end Atlas.Chevalley
