import Atlas.LinearGroups.Chevalley.PositiveWitnessedAscendingCellMultiplication
import Atlas.LinearGroups.Chevalley.PositiveWitnessedStandardParabolic
import Atlas.LinearGroups.Chevalley.RootData.RootParabolicAdjacency

/-! A normal subgroup's B-overgroup cannot stop across an actual nonzero
Cartan edge. The proof uses ascending cells and an outside-node coefficient,
not a BN-pair axiom, a recognition theorem or a simplicity assumption. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData
open scoped Pointwise

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (K : Type*) [Field K]

theorem weightCompanion_simple_conjugate_cell_mem_of_adjacent
    (hdiamond : SimpleDiamondProducts P b)
    (i j : b.support) (hij : i ≠ j) (hcartan : b.cartanMatrix i j ≠ 0)
    (g : WeightCompanion P b O hc hm K)
    (hg : g ∈ DoubleCoset.doubleCoset (weightCompanionWeyl P b O hc hm K i 1)
      (positiveWitnessedTorusJoin P b O hc hm K)
      (positiveWitnessedTorusJoin P b O hc hm K)) :
    weightCompanionWeyl P b O hc hm K j 1 * g *
        (weightCompanionWeyl P b O hc hm K j 1)⁻¹ ∈
      DoubleCoset.doubleCoset
        (weightCompanionWeyl P b O hc hm K j 1 *
          weightCompanionWeyl P b O hc hm K i 1 *
          (weightCompanionWeyl P b O hc hm K j 1)⁻¹)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  let ni := weightCompanionSimpleWeylInN P b O hc hm K i
  let nj := weightCompanionSimpleWeylInN P b O hc hm K j
  have hji : b.cartanMatrix j i ≠ 0 := by
    intro hz
    exact hcartan (b.cartanMatrix_apply_eq_zero_iff_symm.mpr hz)
  have hp₁ : b.IsPos (weightCompanionNRootPermHom P b O hc hm K (nj⁻¹)⁻¹ i.val) := by
    simpa only [ni, nj, inv_inv, weightCompanionNRootPermHom_simple] using
      (b.isPos_of_mem_support i.property).reflectionPerm j.property
        (fun he => hij (Subtype.ext he))
  have hp₂ : b.IsPos (weightCompanionNRootPermHom P b O hc hm K
      (ni * nj⁻¹)⁻¹ j.val) := by
    simpa only [ni, nj, map_inv, map_mul, weightCompanionNRootPermHom_simple,
      mul_inv_rev, inv_inv, P.reflectionPerm_inv, Equiv.Perm.mul_apply] using
      simple_adjacent_double_reflection_isPos P b i j hij hji
  have hfirst : g * nj.val⁻¹ ∈ DoubleCoset.doubleCoset (ni.val * nj.val⁻¹) B B := by
    exact positiveWitnessed_simple_doubleCoset_mul_weyl_subset_of_positive
      P b O hc hm K hdiamond i nj⁻¹ hp₁
      ⟨g, hg, nj.val⁻¹, DoubleCoset.mem_doubleCoset_self B B _, rfl⟩
  have hsecond := positiveWitnessed_simple_doubleCoset_mul_weyl_subset_of_positive
    P b O hc hm K hdiamond j (ni * nj⁻¹) hp₂
    (show nj.val * (g * nj.val⁻¹) ∈ _ from
      ⟨nj.val, DoubleCoset.mem_doubleCoset_self B B _, g * nj.val⁻¹, hfirst, rfl⟩)
  change nj.val * g * nj.val⁻¹ ∈ DoubleCoset.doubleCoset
    (nj.val * ni.val * nj.val⁻¹) B B
  change nj.val * (g * nj.val⁻¹) ∈ DoubleCoset.doubleCoset
    (nj.val * (ni.val * nj.val⁻¹)) B B at hsecond
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hsecond

variable [Fintype κ]

/-- If A is normal and its B-overgroup is P_J, then J is closed under
nonzero Cartan adjacency. The structural equality is supplied by the actual
B-overgroup classification; no irreducibility premise is needed here. -/
theorem normal_sup_positiveWitnessedTorusJoin_parabolic_adjacent_closed
    (hdiamond : SimpleDiamondProducts P b)
    (A : Subgroup (WeightCompanion P b O hc hm K)) [A.Normal]
    (J : Finset b.support)
    (hJ : A ⊔ positiveWitnessedTorusJoin P b O hc hm K =
      positiveWitnessedStandardParabolic P b O hc hm K J)
    (i : b.support) (hi : i ∈ J) (j : b.support)
    (hcartan : b.cartanMatrix i j ≠ 0) : j ∈ J := by
  by_contra hj
  have hij : i ≠ j := fun he => hj (he ▸ hi)
  let B := positiveWitnessedTorusJoin P b O hc hm K
  let ni := weightCompanionSimpleWeylInN P b O hc hm K i
  let nj := weightCompanionSimpleWeylInN P b O hc hm K j
  have hni : ni.val ∈ A ⊔ B := by
    rw [hJ]
    exact weightCompanionWeyl_mem_standardParabolic P b O hc hm K J i hi
  have hprod : ni.val ∈ (A : Set (WeightCompanion P b O hc hm K)) *
      (B : Set (WeightCompanion P b O hc hm K)) := by
    rw [← Subgroup.normal_mul]
    exact hni
  obtain ⟨k, hk, d, hd, hkd⟩ := hprod
  have hkcell : k ∈ DoubleCoset.doubleCoset ni.val B B := by
    apply DoubleCoset.mem_doubleCoset.mpr
    refine ⟨1, B.one_mem, d⁻¹, B.inv_mem hd, ?_⟩
    rw [← hkd]
    group
  have hconjA : nj.val * k * nj.val⁻¹ ∈ A :=
    (inferInstance : A.Normal).conj_mem k hk nj.val
  have hconjP : nj.val * k * nj.val⁻¹ ∈
      positiveWitnessedStandardParabolic P b O hc hm K J := by
    rw [← hJ]
    exact (show A ≤ A ⊔ B from le_sup_left) hconjA
  have hcell := weightCompanion_simple_conjugate_cell_mem_of_adjacent
    P b O hc hm K hdiamond i j hij hcartan k hkcell
  let w := simpleWeylReflection P b j * simpleWeylReflection P b i *
    simpleWeylReflection P b j
  have hperm : weightCompanionNRootPermHom P b O hc hm K
      (nj * ni * nj⁻¹) = w.val := by
    change weightCompanionNRootPermHom P b O hc hm K (nj * ni * nj⁻¹) =
      P.reflectionPerm j.val * P.reflectionPerm i.val * P.reflectionPerm j.val
    simp only [nj, ni, map_mul, map_inv, weightCompanionNRootPermHom_simple,
      P.reflectionPerm_inv]
  have hcanonical : nj.val * k * nj.val⁻¹ ∈
      positiveWitnessedWeylCell P b O hc hm K w := by
    rw [← positiveWitnessedWeylCell_eq_of_lift
      P b O hc hm K hdiamond w (nj * ni * nj⁻¹) hperm]
    exact hcell
  have hw := (mem_standardParabolic_iff_of_mem_weylCell
    P b O hc hm K hdiamond J w _ hcanonical).mp hconjP
  exact conjugated_adjacent_simple_not_mem_rootParabolic P b J i j hj hij hcartan hw

end Atlas.Chevalley
