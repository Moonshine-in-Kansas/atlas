import Atlas.LinearGroups.Chevalley.PositiveRootAdjointHeight
import Atlas.LinearGroups.Chevalley.PositiveRootMinusculeHeight

/-! Positive-root triangularity on the complete faithful companion matrix.
Every specified witness is covered; no canonical root-subgroup or Bruhat
normal-form assertion is made. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hc : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hm : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (R : Type*) [CommRing R] [Nontrivial R] [Fintype κ]

/-- The fixed integral grading on the actual direct sum of all companion blocks. -/
def weightCompanionHeight : WeightCompanionCoordinates P b O → ℤ
  | ⟨none, r⟩ => geckHeight P b r
  | ⟨some k, μ⟩ => weightHeight P b μ.val

/-- All actual companion blocks are unitriangular for every positive witness. -/
theorem weightCompanion_rootLiftHom_heightUnitriangular
    (hdiamond : SimpleDiamondProducts P b) {β : ι}
    (hβ : b.IsPos β) (L : WeightCompanionRootLift P b O hc hm R β)
    (t : Multiplicative R) :
    Atlas.Matrix.HeightUnitriangular (weightCompanionHeight P b O)
      (weightCompanionMatrixRepresentation P b O hc hm R
        (weightCompanionRootLiftHom P b O hc hm R L t)).val := by
  rintro ⟨a, r⟩ ⟨c, s⟩ hle
  by_cases hac : a = c
  · subst c
    have hone : (1 : Matrix (WeightCompanionCoordinates P b O) (WeightCompanionCoordinates P b O) R) ⟨a, r⟩ ⟨a, s⟩ =
        (1 : Matrix (WeightCompanionBlock P b O a) _ R) r s := by
      simp [Matrix.one_apply, Sigma.mk.inj_iff]
    rw [weightCompanionMatrixRepresentation_block, hone]
    cases a with
    | none =>
      exact weightCompanionRho_rootLiftHom_heightUnitriangular
        P b R O hc hm hβ L t r s hle
    | some k =>
      exact weightCompanion_rootLiftHom_minuscule_heightUnitriangular
        P b O hc hm R hdiamond hβ L k t r s hle
  · rw [weightCompanionMatrixRepresentation_off_block P b O hc hm R _ hac]
    have hne : (⟨a, r⟩ : WeightCompanionCoordinates P b O) ≠ ⟨c, s⟩ := by
      intro he
      exact hac (congrArg Sigma.fst he)
    simp only [Matrix.one_apply, if_neg hne]

/-- The complete actual matrix and its inverse belong to the fixed
height-unitriangular subgroup; finiteness is only of the chosen block family. -/
theorem weightCompanion_rootLiftHom_mem_heightUnitriangular
    (hdiamond : SimpleDiamondProducts P b) {β : ι}
    (hβ : b.IsPos β) (L : WeightCompanionRootLift P b O hc hm R β)
    (t : Multiplicative R) :
    weightCompanionMatrixRepresentation P b O hc hm R
      (weightCompanionRootLiftHom P b O hc hm R L t) ∈
        Atlas.Matrix.heightUnitriangularSubgroup (weightCompanionHeight P b O) := by
  refine ⟨weightCompanion_rootLiftHom_heightUnitriangular
    P b O hc hm R hdiamond hβ L t, ?_⟩
  have hinv := weightCompanion_rootLiftHom_heightUnitriangular
    P b O hc hm R hdiamond hβ L t⁻¹
  have he : weightCompanionMatrixRepresentation P b O hc hm R
      (weightCompanionRootLiftHom P b O hc hm R L t⁻¹) =
      (weightCompanionMatrixRepresentation P b O hc hm R
        (weightCompanionRootLiftHom P b O hc hm R L t))⁻¹ :=
    map_inv ((weightCompanionMatrixRepresentation P b O hc hm R).comp
      (weightCompanionRootLiftHom P b O hc hm R L)) t
  change Atlas.Matrix.HeightUnitriangular _
    ((weightCompanionMatrixRepresentation P b O hc hm R
      (weightCompanionRootLiftHom P b O hc hm R L t))⁻¹).val
  rw [← he]
  exact hinv

end Atlas.Chevalley
