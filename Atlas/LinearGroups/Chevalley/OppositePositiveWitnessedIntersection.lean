import Atlas.LinearGroups.Chevalley.NegativeRootAdjointHeight
import Atlas.LinearGroups.Chevalley.PositiveRootNormalizerTransport
import Atlas.LinearGroups.Chevalley.PositiveWitnessedAdjointInjective
import Atlas.LinearGroups.Chevalley.PositiveWitnessedTorusJoin
import Atlas.LinearGroups.Chevalley.WeightCompanionTorusOrder
import Atlas.LinearGroups.Chevalley.WeightCompanionTitsLift
import Atlas.LinearGroups.Chevalley.RootData.RootWeylLongest

/-! The actual longest-lift conjugate of the positive subgroup meets U*T
trivially. The proof uses opposite adjoint triangularity and faithfulness only
on U, not a global adjoint-kernel theorem or a Bruhat/group-order assertion. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData Atlas.GroupTheory
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

/-- Every actual normalizer element taking positive roots to negative roots
conjugates U into the lower-unitriangular adjoint subgroup. -/
theorem positiveWitnessed_conjugate_adjoint_neg_heightUnitriangular
    (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)
    (hneg : ∀ β : ι, b.IsPos β →
      ¬ b.IsPos (weightCompanionNRootPermHom P b O hc hm R n β))
    (u : WeightCompanion P b O hc hm R)
    (hu : u ∈ positiveWitnessedWeightCompanionSubgroup P b O hc hm R) :
    Atlas.Matrix.HeightUnitriangular (fun a => -geckHeight P b a)
      (weightCompanionRho P b O hc hm R (n.val * u * n.val⁻¹)).val.val := by
  let f := ((adjointSubgroup P b R).subtype.comp
    (weightCompanionRho P b O hc hm R)).comp (MulAut.conj n.val).toMonoidHom
  have hle : positiveWitnessedWeightCompanionSubgroup P b O hc hm R ≤
      (Atlas.Matrix.heightUnitriangularSubgroup (fun a => -geckHeight P b a)).comap f := by
    rw [positiveWitnessedWeightCompanionSubgroup, Subgroup.closure_le]
    rintro g ⟨β, hβ, L, t, rfl⟩
    change (weightCompanionRho P b O hc hm R
      (n.val * weightCompanionRootLiftHom P b O hc hm R L t * n.val⁻¹)).val ∈
        Atlas.Matrix.heightUnitriangularSubgroup (fun a => -geckHeight P b a)
    rw [← weightCompanionRootLiftHom_normalizerMul P b O hc hm R L n t]
    exact weightCompanionRho_rootLiftHom_mem_neg_heightUnitriangular
      P b R O hc hm (hneg β hβ)
      (weightCompanionRootLift_normalizerMul P b O hc hm R L n) t
  exact (hle hu).1

/-- The opposite subgroup is a literal conjugate inside the same companion. -/
def oppositePositiveWitnessedWeightCompanionSubgroup :
    Subgroup (WeightCompanion P b O hc hm R) :=
  conjugateSubgroup (weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)).val
    (positiveWitnessedWeightCompanionSubgroup P b O hc hm R)

theorem oppositePositiveWitnessed_adjoint_neg_heightUnitriangular
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ oppositePositiveWitnessedWeightCompanionSubgroup P b O hc hm R) :
    Atlas.Matrix.HeightUnitriangular (fun a => -geckHeight P b a)
      (weightCompanionRho P b O hc hm R g).val.val := by
  obtain ⟨u, hu, he⟩ := hg
  change (weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)).val * u *
    (weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)).val⁻¹ = g at he
  rw [← he]
  apply positiveWitnessed_conjugate_adjoint_neg_heightUnitriangular P b O hc hm R _ _ u hu
  intro β hβ
  rw [weightCompanionNRootPermHom_titsLift]
  exact rootWeylLongest_not_isPos P b hβ

/-- Upper triangularity of U*T uses normalization for the factorization and
the literal diagonal torus formula. Neither finite weight index nor diamond
or collection is needed for this matrix assertion. -/
theorem positiveWitnessedTorusJoin_adjoint_upper
    (g : WeightCompanion P b O hc hm R)
    (hg : g ∈ positiveWitnessedTorusJoin P b O hc hm R)
    (row col : b.support ⊕ ι) (hheight : geckHeight P b row ≤ geckHeight P b col)
    (hne : row ≠ col) : (weightCompanionRho P b O hc hm R g).val.val row col = 0 := by
  have hg' : g ∈
      (positiveWitnessedWeightCompanionSubgroup P b O hc hm R :
        Set (WeightCompanion P b O hc hm R)) *
        (weightCompanionTorusSubgroup P b O hc hm R :
          Set (WeightCompanion P b O hc hm R)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)]
    exact hg
  obtain ⟨u, hu, t, ht, rfl⟩ := hg'
  rw [weightCompanionTorusSubgroup_eq_range] at ht
  obtain ⟨v, rfl⟩ := ht
  change ((weightCompanionRho P b O hc hm R u).val.val *
    ((weightCompanionTorusProduct P b O hc hm R Finset.univ v).val.1).val.val) row col = 0
  rw [weightCompanionTorusProduct_adjoint, adjointTorusProduct_matrix, Matrix.mul_diagonal]
  rw [positiveWitnessedWeightCompanion_adjointHeightUnitriangular P b O hc hm R u hu
    row col hheight]
  simp only [Matrix.one_apply_ne hne, zero_mul]

/-- Opposite and upper triangularity force the adjoint matrix to be one;
conjugation back into U then uses its established injective adjoint projection. -/
theorem oppositePositiveWitnessed_eq_one_of_mem_torusJoin
    (hdiamond : SimpleDiamondProducts P b)
    (g : WeightCompanion P b O hc hm R)
    (hop : g ∈ oppositePositiveWitnessedWeightCompanionSubgroup P b O hc hm R)
    (hb : g ∈ positiveWitnessedTorusJoin P b O hc hm R) : g = 1 := by
  have hlow := oppositePositiveWitnessed_adjoint_neg_heightUnitriangular P b O hc hm R g hop
  have hrho : weightCompanionRho P b O hc hm R g = 1 := by
    apply Subtype.ext
    apply Units.ext
    ext row col
    by_cases h : geckHeight P b col ≤ geckHeight P b row
    · exact hlow row col (by dsimp only; omega)
    · have hlt : geckHeight P b row < geckHeight P b col := by omega
      have hne : row ≠ col := by intro he; subst col; omega
      rw [positiveWitnessedTorusJoin_adjoint_upper P b O hc hm R g hb
        row col hlt.le hne]
      exact (Matrix.one_apply_ne hne).symm
  obtain ⟨u, hu, he⟩ := hop
  let n := (weightCompanionTitsLift P b O hc hm R (rootWeylLongest P b)).val
  change n * u * n⁻¹ = g at he
  have heρ : weightCompanionRho P b O hc hm R n *
      weightCompanionRho P b O hc hm R u *
      (weightCompanionRho P b O hc hm R n)⁻¹ = 1 := by
    rw [← he] at hrho
    simpa only [map_mul, map_inv] using hrho
  have huρ : weightCompanionRho P b O hc hm R u = 1 := by
    calc
      weightCompanionRho P b O hc hm R u =
        (weightCompanionRho P b O hc hm R n)⁻¹ *
          (weightCompanionRho P b O hc hm R n *
            weightCompanionRho P b O hc hm R u *
            (weightCompanionRho P b O hc hm R n)⁻¹) *
          weightCompanionRho P b O hc hm R n := by group
      _ = 1 := by rw [heρ]; group
  have hu1 := positiveWitnessedWeightCompanion_eq_one_of_rho_eq_one
    P b O hc hm R hdiamond u hu huρ
  rw [← he, hu1]
  simp

theorem oppositePositiveWitnessed_inf_torusJoin_eq_bot
    (hdiamond : SimpleDiamondProducts P b) :
    oppositePositiveWitnessedWeightCompanionSubgroup P b O hc hm R ⊓
      positiveWitnessedTorusJoin P b O hc hm R = ⊥ := by
  apply bot_unique
  rintro g ⟨hop, hb⟩
  exact Subgroup.mem_bot.mpr
    (oppositePositiveWitnessed_eq_one_of_mem_torusJoin P b O hc hm R hdiamond g hop hb)

end Atlas.Chevalley
