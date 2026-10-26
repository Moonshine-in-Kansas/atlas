import Atlas.LinearGroups.Chevalley.WeightCompanionCartanBlock
import Atlas.LinearGroups.Chevalley.PositiveRootWeylLifts
import Atlas.LinearGroups.Chevalley.RootData.SimpleReflectionLength

/-! A scalar-faithful Cartan column for each actual witnessed root operator.
This supplies separation of its first-degree coefficient without a field assumption. -/

noncomputable section
open scoped Matrix
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- Any invertible actual adjoint matrix carries a literal Cartan basis vector
to a vector with trivial scalar annihilator, including over rings with zero divisors. -/
theorem adjoint_cartanVector_smul_eq_zero_iff
    (g : Adjoint P b R) (i : b.support) (s : R) :
    s • (g.val.val *ᵥ cartanVector P b R i) = 0 ↔ s = 0 := by
  have hinv : (g⁻¹).val.val * g.val.val = 1 := g.val.inv_val
  constructor
  · intro h
    have hi := congrArg (fun v : b.support ⊕ ι → R => (g⁻¹).val.val *ᵥ v) h
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hinv,
      Matrix.one_mulVec, Matrix.mulVec_zero] at hi
    have hc := congrFun hi (Sum.inl i)
    simpa [cartanVector_eq_single, Pi.single_apply] using hc
  · rintro rfl
    exact zero_smul R _

/-- The actual conjugated simple raising operator sends the transformed negative
simple root vector to the transformed simple Cartan vector. -/
theorem adjoint_conjugate_raising_transformed_negative
    (g : Adjoint P b R) (i : b.support) :
    (g.val.val * raisingOver P b R i * (g⁻¹).val.val) *ᵥ
        (g.val.val *ᵥ rootVector P b R (P.reflectionPerm i.val i.val)) =
      g.val.val *ᵥ cartanVector P b R i := by
  have hinv : (g⁻¹).val.val * g.val.val = 1 := g.val.inv_val
  have hnegative : raisingOver P b R i *ᵥ
      rootVector P b R (P.reflectionPerm i.val i.val) = cartanVector P b R i := by
    simpa [RootPairing.indexNeg_neg] using raisingDividedOver_negative P b R i 1
  have hcancel : (g⁻¹).val.val *ᵥ
      (g.val.val *ᵥ rootVector P b R (P.reflectionPerm i.val i.val)) =
      rootVector P b R (P.reflectionPerm i.val i.val) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, hcancel, ← Matrix.mulVec_mulVec, hnegative]

/-- The corresponding literal root column is a unit multiple of that Cartan
vector whenever the actual matrix has the specified signed root action. -/
theorem adjoint_conjugate_raising_negativeRootColumn
    (g : Adjoint P b R) (w : Equiv.Perm ι)
    (hg : AdjointRootPermutation P b R g w) (i : b.support) :
    ∃ a : Rˣ,
      (g.val.val * raisingOver P b R i * (g⁻¹).val.val) *ᵥ
          rootVector P b R (w (P.reflectionPerm i.val i.val)) =
        a.val • (g.val.val *ᵥ cartanVector P b R i) := by
  obtain ⟨a, ha⟩ := hg (P.reflectionPerm i.val i.val)
  have he := adjoint_conjugate_raising_transformed_negative P b R g i
  rw [ha, Matrix.mulVec_smul] at he
  refine ⟨a⁻¹, ?_⟩
  have hi := congrArg (fun v : b.support ⊕ ι → R => (a⁻¹).val • v) he
  simpa only [smul_smul, Units.inv_mul, one_smul] using hi

variable (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  [Nontrivial R]

/-- The actual N permutation carries opposite roots to opposite roots. This is
only a root-label statement, derived from the existing simple-reflection word. -/
theorem weightCompanionNRootPermHom_opposition
    (n : weightCompanionExtendedWeylSubgroup P b O hclosed hmin R) (β : ι) :
    weightCompanionNRootPermHom P b O hclosed hmin R n (P.reflectionPerm β β) =
      P.reflectionPerm (weightCompanionNRootPermHom P b O hclosed hmin R n β)
        (weightCompanionNRootPermHom P b O hclosed hmin R n β) := by
  have hn := (weightCompanionNRootPerm_spec P b O hclosed hmin R n).1
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b
    (simpleRootPermutationSubgroup_le_weylImage P b hn)
  have he := congrArg (fun w : Equiv.Perm ι => w (simpleReflectionWord P b l β))
    (simpleReflectionWord_conjugate P b l β)
  have hw : simpleReflectionWord P b l (P.reflectionPerm β β) =
      P.reflectionPerm (simpleReflectionWord P b l β)
        (simpleReflectionWord P b l β) := by
    simpa [Equiv.Perm.mul_apply] using he.symm
  rw [hl] at hw
  exact hw

/-- The negative-β column of the literal first-degree root operator is a unit
multiple of the actual transformed Cartan vector from its retained lift witness. -/
theorem weightCompanionRootLift_raising_negativeColumn {β : ι}
    (L : WeightCompanionRootLift P b O hclosed hmin R β) :
    ∃ a : Rˣ,
      let g := weightCompanionRho P b O hclosed hmin R L.lift.val
      (g.val.val * raisingOver P b R L.simple * (g⁻¹).val.val) *ᵥ
          rootVector P b R (P.reflectionPerm β β) =
        a.val • (g.val.val *ᵥ cartanVector P b R L.simple) := by
  have hn := (weightCompanionNRootPerm_spec P b O hclosed hmin R L.lift).2
  have hw : weightCompanionNRootPerm P b O hclosed hmin R L.lift
      (P.reflectionPerm L.simple.val L.simple.val) = P.reflectionPerm β β := by
    change weightCompanionNRootPermHom P b O hclosed hmin R L.lift
      (P.reflectionPerm L.simple.val L.simple.val) = _
    rw [weightCompanionNRootPermHom_opposition, L.root_eq]
  simpa only [hw] using adjoint_conjugate_raising_negativeRootColumn P b R
    (weightCompanionRho P b O hclosed hmin R L.lift.val)
    (weightCompanionNRootPerm P b O hclosed hmin R L.lift) hn L.simple

/-- No nonzero scalar can kill that actual first-degree negative-root column.
This separates its coefficient over every nontrivial commutative ring, without
division by the Cartan integer 2 or any field assumption. -/
theorem weightCompanionRootLift_raising_negativeColumn_smul_eq_zero_iff {β : ι}
    (L : WeightCompanionRootLift P b O hclosed hmin R β) (s : R) :
    let g := weightCompanionRho P b O hclosed hmin R L.lift.val
    s • ((g.val.val * raisingOver P b R L.simple * (g⁻¹).val.val) *ᵥ
      rootVector P b R (P.reflectionPerm β β)) = 0 ↔ s = 0 := by
  dsimp only
  obtain ⟨a, ha⟩ := weightCompanionRootLift_raising_negativeColumn P b R O hclosed hmin L
  dsimp only at ha
  rw [ha, smul_smul, adjoint_cartanVector_smul_eq_zero_iff]
  constructor
  · intro h
    calc
      s = (s * a.val) * a.inv := by rw [mul_assoc, a.val_inv, mul_one]
      _ = 0 := by rw [h, zero_mul]
  · rintro rfl
    exact zero_mul _

end Atlas.Chevalley
