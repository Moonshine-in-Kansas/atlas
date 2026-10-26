import Atlas.LinearAlgebra.HeightUnitriangularConjugate
import Atlas.LinearGroups.Chevalley.Integral.WeylTransportedHeight
import Atlas.LinearGroups.Chevalley.WeightCompanionCartanBlock
import Atlas.LinearGroups.Chevalley.PositiveRootWeylLifts
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength

/-! Every witnessed positive-root map is unitriangular on the entire adjoint
space. The Cartan block is controlled separately from the root-coordinate lines. -/

noncomputable section
open scoped Matrix
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- An actual unit-monomial root action determines the complete support of
each root column, including its zero Cartan coordinates. -/
theorem adjointRootPermutation_nonzero_rootColumn
    {g : Adjoint P b R} {w : Equiv.Perm ι}
    (hg : AdjointRootPermutation P b R g w)
    (row : b.support ⊕ ι) (col : ι)
    (hne : g.val.val row (Sum.inr col) ≠ 0) : row = Sum.inr (w col) := by
  obtain ⟨a, ha⟩ := hg col
  have he := congrFun ha row
  rw [rootVector_eq_single, Matrix.mulVec_single_one, rootVector_eq_single] at he
  by_contra h
  apply hne
  simpa [Matrix.col, Pi.single_apply, h] using he

/-- A root-permuting matrix preserving the Cartan block transports the entire
adjoint grading, not just its root-basis restriction. -/
theorem adjointRootPermutation_wordHeight_support
    {g : Adjoint P b R} (l : List b.support)
    (hg : AdjointRootPermutation P b R g (simpleReflectionWord P b l))
    (hc : AdjointCartanBlockZero P b R g) :
    ∀ row col, g.val.val row col ≠ 0 →
      geckHeight P b row = geckWordHeight P b l col := by
  intro row col hne
  cases col with
  | inl c =>
    cases row with
    | inl r => rfl
    | inr r => exact (hne (hc r c)).elim
  | inr c =>
    have hr := adjointRootPermutation_nonzero_rootColumn P b R hg row c hne
    subst row
    rfl

/-- The inverse full matrix transports the same grading in the reverse direction. -/
theorem adjointRootPermutation_inverse_wordHeight_support
    {g : Adjoint P b R} (l : List b.support)
    (hg : AdjointRootPermutation P b R g (simpleReflectionWord P b l))
    (hc : AdjointCartanBlockZero P b R g⁻¹) :
    ∀ row col, (g⁻¹).val.val row col ≠ 0 →
      geckWordHeight P b l row = geckHeight P b col := by
  intro row col hne
  cases col with
  | inl c =>
    cases row with
    | inl r => rfl
    | inr r => exact (hne (hc r c)).elim
  | inr c =>
    have hr := adjointRootPermutation_nonzero_rootColumn P b R
      (adjointRootPermutation_inv P b R hg) row c hne
    subst row
    simp [geckWordHeight, geckHeight]

/-- Conjugating an actual simple root element along a Weyl word with positive
root image gives an actual height-unitriangular adjoint matrix in every characteristic. -/
theorem adjoint_conjugate_X_heightUnitriangular
    (g : Adjoint P b R) (l : List b.support)
    (hg : AdjointRootPermutation P b R g (simpleReflectionWord P b l))
    (hc : g ∈ adjointCartanBlockSubgroup P b R)
    (i : b.support) (hi : b.IsPos (simpleReflectionWord P b l i.val)) (t : R) :
    Atlas.Matrix.HeightUnitriangular (geckHeight P b)
      ((g * adjointX P b R i t * g⁻¹).val.val) := by
  change Atlas.Matrix.HeightUnitriangular (geckHeight P b)
    (g.val.val * raisingExponential P b R i t * (g⁻¹).val.val)
  exact Atlas.Matrix.HeightUnitriangular.conj_of_height_transport
    (raisingExponential_wordHeightUnitriangular P b R l i hi t)
    (adjointRootPermutation_wordHeight_support P b R l hg hc.1)
    (adjointRootPermutation_inverse_wordHeight_support P b R l hg hc.2)
    g.val.val_inv

variable (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  [Nontrivial R]

/-- Every already-defined witnessed positive-root family is unitriangular on
its complete adjoint summand. Its lift remains explicit; no lift independence,
global projection injectivity, positive-root collection or Bruhat theorem is assumed. -/
theorem weightCompanionRho_rootLiftHom_heightUnitriangular {β : ι}
    (hβ : b.IsPos β) (L : WeightCompanionRootLift P b O hclosed hmin R β)
    (t : Multiplicative R) :
    Atlas.Matrix.HeightUnitriangular (geckHeight P b)
      ((weightCompanionRho P b O hclosed hmin R
        (weightCompanionRootLiftHom P b O hclosed hmin R L t)).val.val) := by
  have hn := weightCompanionNRootPerm_spec P b O hclosed hmin R L.lift
  have hw := simpleRootPermutationSubgroup_le_weylImage P b hn.1
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b hw
  have hg : AdjointRootPermutation P b R
      (weightCompanionRho P b O hclosed hmin R L.lift.val)
      (simpleReflectionWord P b l) := by
    rw [hl]
    exact hn.2
  have hi : b.IsPos (simpleReflectionWord P b l L.simple.val) := by
    rw [hl]
    change b.IsPos (weightCompanionNRootPermHom P b O hclosed hmin R L.lift L.simple.val)
    rw [L.root_eq]
    exact hβ
  have hc := weightCompanionExtendedWeyl_le_cartanBlock P b R O hclosed hmin L.lift.property
  simpa only [weightCompanionRootLiftHom_apply, map_mul, map_inv, weightCompanionRho_X] using
    adjoint_conjugate_X_heightUnitriangular P b R
      (weightCompanionRho P b O hclosed hmin R L.lift.val) l hg hc L.simple hi t.toAdd

/-- The inverse is covered by the same positive-root family with the negative
additive parameter; both directions belong to the actual unitriangular subgroup. -/
theorem weightCompanionRho_rootLiftHom_mem_heightUnitriangular {β : ι}
    (hβ : b.IsPos β) (L : WeightCompanionRootLift P b O hclosed hmin R β)
    (t : Multiplicative R) :
    (weightCompanionRho P b O hclosed hmin R
      (weightCompanionRootLiftHom P b O hclosed hmin R L t)).val ∈
        Atlas.Matrix.heightUnitriangularSubgroup (geckHeight P b) := by
  refine ⟨weightCompanionRho_rootLiftHom_heightUnitriangular P b R O hclosed hmin hβ L t, ?_⟩
  have hinv := weightCompanionRho_rootLiftHom_heightUnitriangular P b R O hclosed hmin hβ L t⁻¹
  have he : weightCompanionRho P b O hclosed hmin R
      (weightCompanionRootLiftHom P b O hclosed hmin R L t⁻¹) =
      (weightCompanionRho P b O hclosed hmin R
        (weightCompanionRootLiftHom P b O hclosed hmin R L t))⁻¹ :=
    map_inv ((weightCompanionRho P b O hclosed hmin R).comp
      (weightCompanionRootLiftHom P b O hclosed hmin R L)) t
  change Atlas.Matrix.HeightUnitriangular (geckHeight P b)
    (((weightCompanionRho P b O hclosed hmin R
      (weightCompanionRootLiftHom P b O hclosed hmin R L t))⁻¹).val.val)
  rw [← he]
  exact hinv

end Atlas.Chevalley
