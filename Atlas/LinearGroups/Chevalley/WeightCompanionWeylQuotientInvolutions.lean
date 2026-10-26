import Atlas.LinearGroups.Chevalley.WeightCompanionWeylSquare
import Atlas.LinearGroups.Chevalley.WeightCompanionExtendedWeyl

/-! The literal simple Weyl cosets in the existing torus quotient square to
one over every commutative ring. This does not assume or construct a
Coxeter system and makes no claim about the kernel of a root-label action. -/

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
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

local instance weylSquareTorusNormal :
    ((weightCompanionTorusSubgroup P b O hclosed hmin R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)).Normal :=
  weightCompanionTorusSubgroup_normal_extendedWeyl P b O hclosed hmin R

/-- Each square already lies in the literal torus, before taking a quotient. -/
theorem weightCompanionWeyl_one_sq_mem_torus (i : b.support) :
    weightCompanionWeyl P b O hclosed hmin R i 1 ^ 2 ∈
      weightCompanionTorusSubgroup P b O hclosed hmin R := by
  rw [weightCompanionWeyl_one_sq]
  exact Subgroup.subset_closure ⟨i, -1, rfl⟩

/-- The literal simple Weyl word's coset in the already defined N/T. -/
def weightCompanionSimpleWeylCoset (i : b.support) :
    (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R ⧸
      (weightCompanionTorusSubgroup P b O hclosed hmin R).subgroupOf
        (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R)) :=
  QuotientGroup.mk'
    ((weightCompanionTorusSubgroup P b O hclosed hmin R).subgroupOf
      (weightCompanionExtendedWeylSubgroup P b O hclosed hmin R))
    ⟨weightCompanionWeyl P b O hclosed hmin R i 1,
      (show weightCompanionWeylSubgroup P b O hclosed hmin R ≤
        weightCompanionExtendedWeylSubgroup P b O hclosed hmin R from le_sup_right)
          (Subgroup.subset_closure ⟨i, rfl⟩)⟩

/-- No characteristic exclusion: each simple Weyl coset squares to one.
This is not an assertion that its order is exactly two over a trivial ring. -/
theorem weightCompanionSimpleWeylCoset_sq (i : b.support) :
    weightCompanionSimpleWeylCoset P b O hclosed hmin R i ^ 2 = 1 := by
  unfold weightCompanionSimpleWeylCoset
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  change weightCompanionWeyl P b O hclosed hmin R i 1 ^ 2 ∈
    weightCompanionTorusSubgroup P b O hclosed hmin R
  exact weightCompanionWeyl_one_sq_mem_torus P b O hclosed hmin R i

theorem weightCompanionSimpleWeylCoset_inv (i : b.support) :
    (weightCompanionSimpleWeylCoset P b O hclosed hmin R i)⁻¹ =
      weightCompanionSimpleWeylCoset P b O hclosed hmin R i := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using weightCompanionSimpleWeylCoset_sq P b O hclosed hmin R i

end Atlas.Chevalley
