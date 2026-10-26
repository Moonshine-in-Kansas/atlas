import Atlas.LinearGroups.Chevalley.PositiveWitnessedAdjointInjective
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusJoin
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusOrder

/-! Adjoint matrices of B=U*T and the adjoint kernel inside B.
No finiteness of the chosen weight family, coefficient field or Bruhat theorem
is needed for these ring-valued statements. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
open scoped Pointwise

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R]

theorem weightCompanionTorus_adjoint_offDiagonal_zero
    (t : WeightCompanion P b O hc hm R)
    (ht : t ∈ weightCompanionTorusSubgroup P b O hc hm R) :
    ∀ row col, row ≠ col →
      (weightCompanionRho P b O hc hm R t).val.val row col = 0 := by
  rw [weightCompanionTorusSubgroup_eq_range] at ht
  obtain ⟨s,rfl⟩ := ht
  change ∀ row col, row ≠ col →
    ((weightCompanionTorusProduct P b O hc hm R Finset.univ s).val.1).val.val row col = 0
  rw [weightCompanionTorusProduct_adjoint, adjointTorusProduct_matrix]
  exact fun row col hne => Matrix.diagonal_apply_ne _ hne

theorem weightCompanionTorus_adjoint_diagonal_ne_zero
    (t : WeightCompanion P b O hc hm R)
    (ht : t ∈ weightCompanionTorusSubgroup P b O hc hm R)
    (row : b.support ⊕ ι) :
    (weightCompanionRho P b O hc hm R t).val.val row row ≠ 0 := by
  let A := (weightCompanionRho P b O hc hm R t).val
  have hprod : (A.val * A.inv) row row = 1 := by
    rw [A.val_inv]
    simp
  have hentry : (A.val * A.inv) row row = A.val row row * A.inv row row := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single row
    · intro col hcol hne
      have hzero := weightCompanionTorus_adjoint_offDiagonal_zero
        P b O hc hm R t ht row col (Ne.symm hne)
      change A.val row col = 0 at hzero
      rw [hzero,zero_mul]
    · simp
  intro hzero
  change A.val row row = 0 at hzero
  rw [hentry,hzero,zero_mul] at hprod
  exact zero_ne_one hprod

/-- Every root diagonal entry of rho(B) is nonzero. Positive factors have
diagonal one and the actual torus has invertible diagonal entries. -/
theorem positiveWitnessedTorusJoin_adjoint_diagonal_ne_zero
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveWitnessedTorusJoin P b O hc hm R)
    (row : b.support ⊕ ι) :
    (weightCompanionRho P b O hc hm R g).val.val row row ≠ 0 := by
  let U := positiveWitnessedWeightCompanionSubgroup P b O hc hm R
  let T := weightCompanionTorusSubgroup P b O hc hm R
  have hprod : g ∈ (U : Set (WeightCompanion P b O hc hm R)) *
      (T : Set (WeightCompanion P b O hc hm R)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U T
      (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)]
    exact hg
  obtain ⟨u,hu,t,ht,rfl⟩ := hprod
  have hentry : (weightCompanionRho P b O hc hm R (u*t)).val.val row row =
      (weightCompanionRho P b O hc hm R t).val.val row row := by
    change ((weightCompanionRho P b O hc hm R u).val.val *
      (weightCompanionRho P b O hc hm R t).val.val) row row = _
    rw [Matrix.mul_apply]
    have hsum := Finset.sum_eq_single row
      (s := (Finset.univ : Finset (b.support ⊕ ι)))
      (f := fun col => (weightCompanionRho P b O hc hm R u).val.val row col *
        (weightCompanionRho P b O hc hm R t).val.val col row)
      (fun col hcol hne => by
        rw [weightCompanionTorus_adjoint_offDiagonal_zero P b O hc hm R t ht col row hne,
          mul_zero]) (by simp)
    rw [hsum,
      (positiveWitnessedWeightCompanion_adjointHeightUnitriangular P b O hc hm R u hu).diagonal,
      one_mul]
  rw [hentry]
  exact weightCompanionTorus_adjoint_diagonal_ne_zero P b O hc hm R t ht row

/-- An N element whose adjoint image lies in rho(B) has trivial Weyl action,
and hence belongs to the already identified torus kernel in N. -/
theorem weightCompanionN_mem_torus_of_rho_eq_B
    (hdiamond : SimpleDiamondProducts P b)
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveWitnessedTorusJoin P b O hc hm R)
    (heq : weightCompanionRho P b O hc hm R n.val = weightCompanionRho P b O hc hm R g) :
    n.val ∈ weightCompanionTorusSubgroup P b O hc hm R := by
  have hperm : weightCompanionNRootPermHom P b O hc hm R n = 1 := by
    apply Equiv.ext
    intro β
    change weightCompanionNRootPerm P b O hc hm R n β = β
    have hnz : (weightCompanionRho P b O hc hm R n.val).val.val
        (Sum.inr β) (Sum.inr β) ≠ 0 := by
      rw [heq]
      exact positiveWitnessedTorusJoin_adjoint_diagonal_ne_zero P b O hc hm R g hg _
    have hlabel := adjointRootPermutation_nonzero_rootColumn P b R
      (weightCompanionNRootPerm_spec P b O hc hm R n).2 (Sum.inr β) β hnz
    exact (Sum.inr.inj hlabel).symm
  have hk : n ∈ (weightCompanionNRootPermHom P b O hc hm R).ker := hperm
  rw [weightCompanionNRootPermHom_ker_eq_torus P b O hc hm R hdiamond] at hk
  exact hk

theorem positiveWitnessedTorusJoin_inf_rhoKernel_le_torus
    (hdiamond : SimpleDiamondProducts P b) :
    positiveWitnessedTorusJoin P b O hc hm R ⊓
      (weightCompanionRho P b O hc hm R).ker ≤ weightCompanionTorusSubgroup P b O hc hm R := by
  rintro g ⟨hg,hker⟩
  let U := positiveWitnessedWeightCompanionSubgroup P b O hc hm R
  let T := weightCompanionTorusSubgroup P b O hc hm R
  have hprod : g ∈ (U : Set (WeightCompanion P b O hc hm R)) *
      (T : Set (WeightCompanion P b O hc hm R)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U T
      (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)]
    exact hg
  obtain ⟨u,hu,t,ht,hut⟩ := hprod
  change u * t = g at hut
  have hker' : weightCompanionRho P b O hc hm R u *
      weightCompanionRho P b O hc hm R t = 1 := by
    rw [← map_mul, hut]
    exact hker
  have hrho : weightCompanionRho P b O hc hm R u =
      weightCompanionRho P b O hc hm R t⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left hker'
  have huone : u = 1 := by
    apply positiveWitnessedWeightCompanion_eq_one_of_adjoint_diagonal P b O hc hm R hdiamond u hu
    rw [hrho]
    exact weightCompanionTorus_adjoint_offDiagonal_zero P b O hc hm R t⁻¹ (T.inv_mem ht)
  rw [huone,one_mul] at hut
  exact hut ▸ ht

end Atlas.Chevalley
