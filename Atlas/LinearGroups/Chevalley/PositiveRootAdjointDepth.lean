import Atlas.LinearAlgebra.HeightDepth
import Atlas.LinearGroups.Chevalley.PositiveRootAdjointHeight

/-! Exact depth and first homogeneous coefficient of a witnessed positive-root
family on its actual adjoint summand. Witnesses remain explicit. No coordinate
uniqueness, root-group coherence, collection or global projection kernel is assumed. -/

noncomputable section
universe u
namespace Atlas.Chevalley
open Classical Integral RootData

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- The actual conjugate of the nth integral divided-power coefficient after
base change. No division is performed in R. -/
def adjointConjugateRaisingDivided (g : Adjoint P b R)
    (i : b.support) (n : ℕ) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  g.val.val * raisingDividedOver P b R i n * (g⁻¹).val.val

theorem adjointConjugateRaisingDivided_one (g : Adjoint P b R) (i : b.support) :
    adjointConjugateRaisingDivided P b R g i 1 =
      g.val.val * raisingOver P b R i * (g⁻¹).val.val := by
  rw [adjointConjugateRaisingDivided, raisingDividedOver_one]

/-- The exact integral support degree survives arbitrary base change. -/
theorem raisingDividedOver_wordHeight_eq_zero_of_degree_ne
    (l : List b.support) (i : b.support) (n : ℕ)
    (row col : b.support ⊕ ι)
    (hne : geckWordHeight P b l row ≠ geckWordHeight P b l col +
      (n : ℤ) * b.height (simpleReflectionWord P b l i.val)) :
    raisingDividedOver P b R i n row col = 0 := by
  have hz : raisingDividedPower P b i n row col = 0 := by
    by_contra h
    exact hne (raisingDividedPower_wordHeight_weightedSupport P b l i n row col h)
  simp only [raisingDividedOver, Matrix.map_apply, hz, map_zero]

/-- Each conjugated coefficient has degree n times the height of the actual
image root, including the Cartan/root transition blocks. -/
theorem adjointConjugateRaisingDivided_eq_zero_of_height_ne
    (g : Adjoint P b R) (l : List b.support)
    (hg : AdjointRootPermutation P b R g (simpleReflectionWord P b l))
    (hc : g ∈ adjointCartanBlockSubgroup P b R)
    (i : b.support) (n : ℕ) (row col : b.support ⊕ ι)
    (hne : geckHeight P b row ≠ geckHeight P b col +
      (n : ℤ) * b.height (simpleReflectionWord P b l i.val)) :
    adjointConjugateRaisingDivided P b R g i n row col = 0 := by
  exact Atlas.Matrix.conjugate_eq_zero_of_height_ne
    (geckHeight P b) (geckWordHeight P b l)
    ((n : ℤ) * b.height (simpleReflectionWord P b l i.val))
    g.val.val (raisingDividedOver P b R i n) (g⁻¹).val.val
    (adjointRootPermutation_wordHeight_support P b R l hg hc.1)
    (adjointRootPermutation_inverse_wordHeight_support P b R l hg hc.2)
    (raisingDividedOver_wordHeight_eq_zero_of_degree_ne P b R l i n)
    row col hne

/-- Conjugation preserves the actual degree-three divided-power expansion. -/
theorem adjoint_conjugate_X_expansion
    (g : Adjoint P b R) (i : b.support) (t : R) :
    (g * adjointX P b R i t * g⁻¹).val.val =
      1 + t • adjointConjugateRaisingDivided P b R g i 1 +
        t ^ 2 • adjointConjugateRaisingDivided P b R g i 2 +
        t ^ 3 • adjointConjugateRaisingDivided P b R g i 3 := by
  have hunit : g.val.val * (g⁻¹).val.val = 1 := g.val.val_inv
  change g.val.val * raisingExponential P b R i t * (g⁻¹).val.val = _
  rw [raisingExponential_expansion]
  simp only [mul_add, add_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul,
    adjointConjugateRaisingDivided, raisingDividedOver_zero,
    raisingDividedOver_one, hunit]

/-- The deviation from the identity starts at the height of the positive
image root, a stronger assertion than strict unitriangularity alone. -/
theorem adjoint_conjugate_X_sub_one_heightAtLeast
    (g : Adjoint P b R) (l : List b.support)
    (hg : AdjointRootPermutation P b R g (simpleReflectionWord P b l))
    (hc : g ∈ adjointCartanBlockSubgroup P b R)
    (i : b.support) (hi : b.IsPos (simpleReflectionWord P b l i.val)) (t : R) :
    Atlas.Matrix.HeightAtLeast (geckHeight P b)
      (b.height (simpleReflectionWord P b l i.val))
      ((g * adjointX P b R i t * g⁻¹).val.val - 1) := by
  intro row col hlt
  have hd : 0 < b.height (simpleReflectionWord P b l i.val) := b.isPos_iff.mp hi
  have hz (n : ℕ) (hn : 0 < n) :
      adjointConjugateRaisingDivided P b R g i n row col = 0 := by
    apply adjointConjugateRaisingDivided_eq_zero_of_height_ne P b R g l hg hc i n
    intro he
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have hmul : b.height (simpleReflectionWord P b l i.val) ≤
        (n : ℤ) * b.height (simpleReflectionWord P b l i.val) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hn' (le_of_lt hd)
    omega
  rw [adjoint_conjugate_X_expansion]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    hz 1 (by decide), hz 2 (by decide), hz 3 (by decide), smul_zero, add_zero, sub_self]

/-- At the first possible height difference, only the linear parameter term
survives. The quadratic and cubic divided powers have strictly greater degree. -/
theorem adjoint_conjugate_X_first_degree
    (g : Adjoint P b R) (l : List b.support)
    (hg : AdjointRootPermutation P b R g (simpleReflectionWord P b l))
    (hc : g ∈ adjointCartanBlockSubgroup P b R)
    (i : b.support) (hi : b.IsPos (simpleReflectionWord P b l i.val))
    (t : R) (row col : b.support ⊕ ι)
    (hdegree : geckHeight P b row = geckHeight P b col +
      b.height (simpleReflectionWord P b l i.val)) :
    ((g * adjointX P b R i t * g⁻¹).val.val - 1) row col =
      t • adjointConjugateRaisingDivided P b R g i 1 row col := by
  have hd : 0 < b.height (simpleReflectionWord P b l i.val) := b.isPos_iff.mp hi
  have h2 : adjointConjugateRaisingDivided P b R g i 2 row col = 0 := by
    apply adjointConjugateRaisingDivided_eq_zero_of_height_ne P b R g l hg hc i 2
    norm_num only [Nat.cast_ofNat]
    omega
  have h3 : adjointConjugateRaisingDivided P b R g i 3 row col = 0 := by
    apply adjointConjugateRaisingDivided_eq_zero_of_height_ne P b R g l hg hc i 3
    norm_num only [Nat.cast_ofNat]
    omega
  rw [adjoint_conjugate_X_expansion]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    h2, h3, smul_zero, add_zero, add_sub_cancel_left]

variable (O : κ → Finset (Integral.Minuscule.WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → Integral.Minuscule.weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (Integral.Minuscule.corootElement P i) = -1 ∨
      μ (Integral.Minuscule.corootElement P i) = 0 ∨
      μ (Integral.Minuscule.corootElement P i) = 1)
  [Nontrivial R]

private theorem rootLift_word_height_data {β : ι}
    (L : WeightCompanionRootLift P b O hclosed hmin R β) :
    ∃ l : List b.support,
      AdjointRootPermutation P b R
        (weightCompanionRho P b O hclosed hmin R L.lift.val)
        (simpleReflectionWord P b l) ∧
      simpleReflectionWord P b l L.simple.val = β := by
  have hn := weightCompanionNRootPerm_spec P b O hclosed hmin R L.lift
  have hw := simpleRootPermutationSubgroup_le_weylImage P b hn.1
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem P b hw
  refine ⟨l, ?_, ?_⟩
  · rw [hl]
    exact hn.2
  · rw [hl]
    exact L.root_eq

/-- The actual adjoint image of each witnessed root parameter starts exactly
at or above its root height. No injectivity of the global projection is assumed. -/
theorem weightCompanionRho_rootLiftHom_sub_one_heightAtLeast {β : ι}
    (hβ : b.IsPos β) (L : WeightCompanionRootLift P b O hclosed hmin R β)
    (t : Multiplicative R) :
    Atlas.Matrix.HeightAtLeast (geckHeight P b) (b.height β)
      ((weightCompanionRho P b O hclosed hmin R
        (weightCompanionRootLiftHom P b O hclosed hmin R L t)).val.val - 1) := by
  obtain ⟨l, hg, hroot⟩ := rootLift_word_height_data P b R O hclosed hmin L
  have hc := weightCompanionExtendedWeyl_le_cartanBlock P b R O hclosed hmin L.lift.property
  have hi : b.IsPos (simpleReflectionWord P b l L.simple.val) := by
    rw [hroot]
    exact hβ
  have he := adjoint_conjugate_X_sub_one_heightAtLeast P b R
    (weightCompanionRho P b O hclosed hmin R L.lift.val) l hg hc L.simple hi t.toAdd
  simpa only [weightCompanionRootLiftHom_apply, map_mul, map_inv, weightCompanionRho_X,
    hroot] using he

/-- The first homogeneous coefficient of the witnessed family is the actual
conjugated raising operator. This is not a root-lift independence assertion. -/
theorem weightCompanionRho_rootLiftHom_first_degree {β : ι}
    (hβ : b.IsPos β) (L : WeightCompanionRootLift P b O hclosed hmin R β)
    (t : Multiplicative R) (row col : b.support ⊕ ι)
    (hdegree : geckHeight P b row = geckHeight P b col + b.height β) :
    ((weightCompanionRho P b O hclosed hmin R
      (weightCompanionRootLiftHom P b O hclosed hmin R L t)).val.val - 1) row col =
      t.toAdd • adjointConjugateRaisingDivided P b R
        (weightCompanionRho P b O hclosed hmin R L.lift.val) L.simple 1 row col := by
  obtain ⟨l, hg, hroot⟩ := rootLift_word_height_data P b R O hclosed hmin L
  have hc := weightCompanionExtendedWeyl_le_cartanBlock P b R O hclosed hmin L.lift.property
  have hi : b.IsPos (simpleReflectionWord P b l L.simple.val) := by
    rw [hroot]
    exact hβ
  have he := adjoint_conjugate_X_first_degree P b R
    (weightCompanionRho P b O hclosed hmin R L.lift.val) l hg hc L.simple hi
    t.toAdd row col (by simpa only [hroot] using hdegree)
  simpa only [weightCompanionRootLiftHom_apply, map_mul, map_inv, weightCompanionRho_X] using he

end Atlas.Chevalley
