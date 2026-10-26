import Atlas.LinearGroups.Chevalley.Integral.NegativeWeylTransportedHeight
import Atlas.LinearGroups.Chevalley.PositiveRootAdjointHeight

/-! Full adjoint lower unitriangularity of retained negative-root families.
The root and Cartan columns are both included. No root coherence, collection,
longest-height formula or faithfulness of the global adjoint projection is used. -/
noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

theorem adjoint_conjugate_X_neg_heightUnitriangular
    (g : Adjoint P b R) (l : List b.support)
    (hg : AdjointRootPermutation P b R g (simpleReflectionWord P b l))
    (hc : g ∈ adjointCartanBlockSubgroup P b R)
    (i : b.support) (hi : ¬ b.IsPos (simpleReflectionWord P b l i.val)) (t : R) :
    Atlas.Matrix.HeightUnitriangular (fun a => -geckHeight P b a)
      ((g * adjointX P b R i t * g⁻¹).val.val) := by
  change Atlas.Matrix.HeightUnitriangular (fun a => -geckHeight P b a)
    (g.val.val * raisingExponential P b R i t * (g⁻¹).val.val)
  apply Atlas.Matrix.HeightUnitriangular.conj_of_height_transport
    (raisingExponential_neg_wordHeightUnitriangular P b R l i hi t)
  · intro row col hne
    exact congrArg Neg.neg
      (adjointRootPermutation_wordHeight_support P b R l hg hc.1 row col hne)
  · intro row col hne
    exact congrArg Neg.neg
      (adjointRootPermutation_inverse_wordHeight_support P b R l hg hc.2 row col hne)
  · exact g.val.val_inv

variable (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  [Nontrivial R]

theorem weightCompanionRho_rootLiftHom_neg_heightUnitriangular {β : ι}
    (hβ : ¬ b.IsPos β) (L : WeightCompanionRootLift P b O hclosed hmin R β)
    (t : Multiplicative R) :
    Atlas.Matrix.HeightUnitriangular (fun a => -geckHeight P b a)
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
  have hi : ¬ b.IsPos (simpleReflectionWord P b l L.simple.val) := by
    rw [hl]
    change ¬ b.IsPos (weightCompanionNRootPermHom P b O hclosed hmin R L.lift L.simple.val)
    rw [L.root_eq]
    exact hβ
  have hc := weightCompanionExtendedWeyl_le_cartanBlock P b R O hclosed hmin L.lift.property
  simpa only [weightCompanionRootLiftHom_apply, map_mul, map_inv, weightCompanionRho_X] using
    adjoint_conjugate_X_neg_heightUnitriangular P b R
      (weightCompanionRho P b O hclosed hmin R L.lift.val) l hg hc L.simple hi t.toAdd

theorem weightCompanionRho_rootLiftHom_mem_neg_heightUnitriangular {β : ι}
    (hβ : ¬ b.IsPos β) (L : WeightCompanionRootLift P b O hclosed hmin R β)
    (t : Multiplicative R) :
    (weightCompanionRho P b O hclosed hmin R
      (weightCompanionRootLiftHom P b O hclosed hmin R L t)).val ∈
        Atlas.Matrix.heightUnitriangularSubgroup (fun a => -geckHeight P b a) := by
  refine ⟨weightCompanionRho_rootLiftHom_neg_heightUnitriangular
    P b R O hclosed hmin hβ L t, ?_⟩
  have hinv := weightCompanionRho_rootLiftHom_neg_heightUnitriangular
    P b R O hclosed hmin hβ L t⁻¹
  have he : weightCompanionRho P b O hclosed hmin R
      (weightCompanionRootLiftHom P b O hclosed hmin R L t⁻¹) =
      (weightCompanionRho P b O hclosed hmin R
        (weightCompanionRootLiftHom P b O hclosed hmin R L t))⁻¹ :=
    map_inv ((weightCompanionRho P b O hclosed hmin R).comp
      (weightCompanionRootLiftHom P b O hclosed hmin R L)) t
  change Atlas.Matrix.HeightUnitriangular (fun a => -geckHeight P b a)
    (((weightCompanionRho P b O hclosed hmin R
      (weightCompanionRootLiftHom P b O hclosed hmin R L t))⁻¹).val.val)
  rw [← he]
  exact hinv

end Atlas.Chevalley
