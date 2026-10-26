import Atlas.LinearGroups.Chevalley.WeightCompanionTorusParameters

/-! Actual rank-one square relation in the full simultaneous companion.
Only the established additive root laws and torus multiplication are used.
No faithfulness, root-label action, Bruhat decomposition or Coxeter presentation
is a premise. All coefficient rings are commutative, without characteristic
or nontriviality restrictions. -/

noncomputable section
namespace Atlas.Chevalley

private theorem square_from_inverse_torus {G : Type*} [Group G] (w h : G)
    (hdef : h = w⁻¹ * w⁻¹) (hh : h * h = 1) : w ^ 2 = h := by
  calc
    w ^ 2 = (w⁻¹ * w⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv, pow_two]
    _ = h⁻¹ := congrArg Inv.inv hdef.symm
    _ = h := inv_eq_of_mul_eq_one_right hh

universe u
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- Negating the unit parameter reverses the actual three-factor Weyl word. -/
theorem weightCompanionWeyl_neg (i : b.support) (t : Rˣ) :
    weightCompanionWeyl P b O hclosed hmin R i (-t) =
      (weightCompanionWeyl P b O hclosed hmin R i t)⁻¹ := by
  have hx (s : R) :
      weightCompanionX P b O hclosed hmin R i (-s) =
        (weightCompanionX P b O hclosed hmin R i s)⁻¹ := by
    exact map_inv (weightCompanionXHom P b O hclosed hmin R i) (Multiplicative.ofAdd s)
  have hy (s : R) :
      weightCompanionY P b O hclosed hmin R i (-s) =
        (weightCompanionY P b O hclosed hmin R i s)⁻¹ := by
    exact map_inv (weightCompanionYHom P b O hclosed hmin R i) (Multiplicative.ofAdd s)
  change
    weightCompanionX P b O hclosed hmin R i (-t.val) *
        weightCompanionY P b O hclosed hmin R i (-(-t.inv)) *
        weightCompanionX P b O hclosed hmin R i (-t.val) =
      (weightCompanionX P b O hclosed hmin R i t.val *
        weightCompanionY P b O hclosed hmin R i (-t.inv) *
        weightCompanionX P b O hclosed hmin R i t.val)⁻¹
  simp only [hx t.val, hy (-t.inv), mul_inv_rev, mul_assoc]

/-- The full companion satisfies the actual rank-one Tits square relation. -/
theorem weightCompanionWeyl_one_sq (i : b.support) :
    weightCompanionWeyl P b O hclosed hmin R i 1 ^ 2 =
      weightCompanionTorus P b O hclosed hmin R i (-1) := by
  apply square_from_inverse_torus
  · rw [weightCompanionTorus, weightCompanionWeyl_neg]
  · rw [← weightCompanionTorus_mul]
    simp only [neg_mul_neg, one_mul, weightCompanionTorus, mul_inv_cancel]

end Atlas.Chevalley
