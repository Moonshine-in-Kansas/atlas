import Atlas.LinearGroups.Chevalley.WeightCompanionWeylTorus
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusKernel

/-! Actual torus normalization. Noncommutative cancellation and closure
arguments are proved first in an abstract group, avoiding simplification of the
large concrete companion subtype. -/
noncomputable section
namespace Atlas.Chevalley

private theorem normalizer_zpow_neg_two_mul {G : Type*} [Group G] (a : G) :
    a ^ (-2 : ℤ) * a = a⁻¹ := by
  simp only [zpow_neg, zpow_ofNat]
  group

private theorem normalizer_conjugate_twice {G : Type*} [Group G]
    (w t c ci : G) (ht : w * t * w⁻¹ = c * t)
    (hc : w * c * w⁻¹ = ci) (hi : ci * c = 1) :
    w * (w * t * w⁻¹) * w⁻¹ = t := by
  rw [ht]
  calc
    w * (c * t) * w⁻¹ = (w * c * w⁻¹) * (w * t * w⁻¹) := by group
    _ = ci * (c * t) := by rw [hc, ht]
    _ = t := by rw [← mul_assoc, hi, one_mul]

private theorem normalizer_inverse_conjugate_of_twice {G : Type*} [Group G]
    (w t : G) (ht : w * (w * t * w⁻¹) * w⁻¹ = t) :
    w⁻¹ * t * w = w * t * w⁻¹ := by
  calc
    w⁻¹ * t * w = w⁻¹ * (w * (w * t * w⁻¹) * w⁻¹) * w :=
      congrArg (fun x : G => w⁻¹ * x * w) ht.symm
    _ = w * t * w⁻¹ := by group

private theorem normalizer_closure_two_sided {G : Type*} [Group G]
    (S : Set G) (w : G)
    (hpos : ∀ g ∈ S, w * g * w⁻¹ ∈ Subgroup.closure S)
    (hneg : ∀ g ∈ S, w⁻¹ * g * w ∈ Subgroup.closure S) :
    w ∈ Subgroup.normalizer (↑(Subgroup.closure S) : Set G) := by
  let T := Subgroup.closure S
  have hp : T ≤ T.comap (MulAut.conj w).toMonoidHom := by
    change Subgroup.closure S ≤ _
    rw [Subgroup.closure_le]
    intro g hg
    exact hpos g hg
  have hm : T ≤ T.comap (MulAut.conj w⁻¹).toMonoidHom := by
    change Subgroup.closure S ≤ _
    rw [Subgroup.closure_le]
    intro g hg
    change w⁻¹ * g * (w⁻¹)⁻¹ ∈ T
    rw [inv_inv]
    exact hneg g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact fun hg => hp hg
  · intro hg
    have hh := hm hg
    change w⁻¹ * (w * g * w⁻¹) * (w⁻¹)⁻¹ ∈ T at hh
    have hc : w⁻¹ * (w * g * w⁻¹) * (w⁻¹)⁻¹ = g := by group
    rwa [hc] at hh

universe u
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

theorem weightCompanionWeyl_conjugate_Torus_same (i : b.support) (a : Rˣ) :
    weightCompanionWeyl P b O hclosed hmin R i 1 *
      weightCompanionTorus P b O hclosed hmin R i a *
        (weightCompanionWeyl P b O hclosed hmin R i 1)⁻¹ =
      weightCompanionTorus P b O hclosed hmin R i a⁻¹ := by
  rw [weightCompanionWeyl_conjugate_Torus, b.cartanMatrix_apply_same,
    ← weightCompanionTorus_mul, normalizer_zpow_neg_two_mul]

/-- The conjugation action on each actual torus generator is an involution. -/
theorem weightCompanionWeyl_conjugate_twice_Torus (i j : b.support) (a : Rˣ) :
    let W := weightCompanionWeyl P b O hclosed hmin R i 1
    W * (W * weightCompanionTorus P b O hclosed hmin R j a * W⁻¹) * W⁻¹ =
      weightCompanionTorus P b O hclosed hmin R j a := by
  let c := a ^ (-b.cartanMatrix i j)
  have hinv : weightCompanionTorus P b O hclosed hmin R i c⁻¹ *
      weightCompanionTorus P b O hclosed hmin R i c = 1 := by
    rw [← weightCompanionTorus_mul, inv_mul_cancel]
    exact mul_inv_cancel _
  exact normalizer_conjugate_twice
    (weightCompanionWeyl P b O hclosed hmin R i 1)
    (weightCompanionTorus P b O hclosed hmin R j a)
    (weightCompanionTorus P b O hclosed hmin R i c)
    (weightCompanionTorus P b O hclosed hmin R i c⁻¹)
    (weightCompanionWeyl_conjugate_Torus P b O hclosed hmin R i j a)
    (weightCompanionWeyl_conjugate_Torus_same P b O hclosed hmin R i c) hinv

/-- Inverse Weyl conjugation has the same reflection action on the torus. -/
theorem weightCompanionWeyl_inv_conjugate_Torus (i j : b.support) (a : Rˣ) :
    (weightCompanionWeyl P b O hclosed hmin R i 1)⁻¹ *
      weightCompanionTorus P b O hclosed hmin R j a *
        weightCompanionWeyl P b O hclosed hmin R i 1 =
      weightCompanionTorus P b O hclosed hmin R i (a ^ (-b.cartanMatrix i j)) *
        weightCompanionTorus P b O hclosed hmin R j a := by
  exact (normalizer_inverse_conjugate_of_twice
    (weightCompanionWeyl P b O hclosed hmin R i 1)
    (weightCompanionTorus P b O hclosed hmin R j a)
    (weightCompanionWeyl_conjugate_twice_Torus P b O hclosed hmin R i j a)).trans
      (weightCompanionWeyl_conjugate_Torus P b O hclosed hmin R i j a)

/-- Both conjugation directions preserve the actual torus closure. -/
theorem weightCompanionWeyl_mem_torusNormalizer (i : b.support) :
    weightCompanionWeyl P b O hclosed hmin R i 1 ∈
      Subgroup.normalizer (↑(weightCompanionTorusSubgroup P b O hclosed hmin R) : Set _) := by
  let T := weightCompanionTorusSubgroup P b O hclosed hmin R
  have generator_mem (j : b.support) (a : Rˣ) :
      weightCompanionTorus P b O hclosed hmin R j a ∈ T :=
    Subgroup.subset_closure ⟨j,a,rfl⟩
  apply normalizer_closure_two_sided
  · rintro g ⟨j,a,rfl⟩
    rw [weightCompanionWeyl_conjugate_Torus]
    exact T.mul_mem (generator_mem _ _) (generator_mem _ _)
  · rintro g ⟨j,a,rfl⟩
    rw [weightCompanionWeyl_inv_conjugate_Torus]
    exact T.mul_mem (generator_mem _ _) (generator_mem _ _)

end Atlas.Chevalley
