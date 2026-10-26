import Atlas.LinearGroups.Chevalley.RootLiftCartanSeparation

/-! Off-diagonal Cartan-column separation of distinct witnessed root labels.
All lift witnesses remain explicit; no collection or uniqueness theorem is assumed. -/

noncomputable section
open scoped Matrix
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

/-- A matrix realizing a signed root permutation has zero Cartan entries in
every root column. This uses the actual column action, not a quotient action. -/
theorem adjointRootPermutation_cartan_rootEntry
    {g : Adjoint P b R} {w : Equiv.Perm ι}
    (hg : AdjointRootPermutation P b R g w) (j : b.support) (β : ι) :
    g.val.val (Sum.inl j) (Sum.inr β) = 0 := by
  obtain ⟨a, ha⟩ := hg β
  have he := congrFun ha (Sum.inl j)
  simpa [rootVector_eq_single, Matrix.mulVec_single_one, Matrix.col,
    Pi.single_apply] using he

/-- The literal simple raising operator has a Cartan component only on its
own negative-root column, over every commutative coefficient ring. -/
theorem raisingOver_rootVector_cartan_eq_zero_of_ne
    (i j : b.support) (β : ι) (hβ : β ≠ P.reflectionPerm i.val i.val) :
    (raisingOver P b R i *ᵥ rootVector P b R β) (Sum.inl j) = 0 := by
  rw [rootVector_eq_single, Matrix.mulVec_single_one]
  change raisingOver P b R i (Sum.inl j) (Sum.inr β) = 0
  simp [raisingOver, raising, RootPairing.GeckConstruction.e,
    RootPairing.indexNeg_neg, hβ]

/-- Root-column preservation sends every vector with zero Cartan coordinates
to another such vector. No Cartan-block action or field hypothesis is needed. -/
theorem adjointRootPermutation_cartan_eq_zero_of_cartan_eq_zero
    {g : Adjoint P b R} {w : Equiv.Perm ι}
    (hg : AdjointRootPermutation P b R g w)
    (v : b.support ⊕ ι → R) (hv : ∀ j : b.support, v (Sum.inl j) = 0)
    (j : b.support) : (g.val.val *ᵥ v) (Sum.inl j) = 0 := by
  change ∑ k, g.val.val (Sum.inl j) k * v k = 0
  apply Finset.sum_eq_zero
  intro k hk
  cases k with
  | inl a => simp only [hv a, mul_zero]
  | inr a => simp only [adjointRootPermutation_cartan_rootEntry P b R hg j a, zero_mul]

/-- A conjugated simple raising matrix has no Cartan component on a root column
other than the image of its own negative simple root. -/
theorem adjoint_conjugate_raising_distinctRoot_cartan_eq_zero
    (g : Adjoint P b R) (w : Equiv.Perm ι)
    (hg : AdjointRootPermutation P b R g w) (i j : b.support)
    (β : ι) (hβ : β ≠ w (P.reflectionPerm i.val i.val)) :
    ((g.val.val * raisingOver P b R i * (g⁻¹).val.val) *ᵥ
      rootVector P b R β) (Sum.inl j) = 0 := by
  obtain ⟨a, ha⟩ := adjointRootPermutation_inv P b R hg β
  have hpre : w⁻¹ β ≠ P.reflectionPerm i.val i.val := by
    intro h
    apply hβ
    calc
      β = w (w⁻¹ β) := (w.apply_symm_apply β).symm
      _ = w (P.reflectionPerm i.val i.val) := congrArg w h
  have he : (g.val.val * raisingOver P b R i * (g⁻¹).val.val) *ᵥ
      rootVector P b R β =
      a.val • (g.val.val *ᵥ (raisingOver P b R i *ᵥ rootVector P b R (w⁻¹ β))) := by
    rw [← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]
  have hz := adjointRootPermutation_cartan_eq_zero_of_cartan_eq_zero P b R hg
    (raisingOver P b R i *ᵥ rootVector P b R (w⁻¹ β))
    (fun c => raisingOver_rootVector_cartan_eq_zero_of_ne P b R i c (w⁻¹ β) hpre) j
  have hc := congrFun he (Sum.inl j)
  simpa only [Pi.smul_apply, hz, smul_zero] using hc

variable (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  [Nontrivial R]

/-- For distinct labels β and γ, the actual γ-witnessed raising operator has
zero Cartan projection on v₋β. No positivity or lift-independence premise is used. -/
theorem weightCompanionRootLift_raising_distinctLabel_cartan_eq_zero
    {β γ : ι} (L : WeightCompanionRootLift P b O hclosed hmin R γ)
    (hβγ : β ≠ γ) (j : b.support) :
    let g := weightCompanionRho P b O hclosed hmin R L.lift.val
    ((g.val.val * raisingOver P b R L.simple * (g⁻¹).val.val) *ᵥ
      rootVector P b R (P.reflectionPerm β β)) (Sum.inl j) = 0 := by
  have hn := (weightCompanionNRootPerm_spec P b O hclosed hmin R L.lift).2
  have hw : weightCompanionNRootPerm P b O hclosed hmin R L.lift
      (P.reflectionPerm L.simple.val L.simple.val) = P.reflectionPerm γ γ := by
    change weightCompanionNRootPermHom P b O hclosed hmin R L.lift
      (P.reflectionPerm L.simple.val L.simple.val) = _
    rw [weightCompanionNRootPermHom_opposition, L.root_eq]
  have hne : P.reflectionPerm β β ≠
      weightCompanionNRootPerm P b O hclosed hmin R L.lift
        (P.reflectionPerm L.simple.val L.simple.val) := by
    rw [hw]
    intro h
    apply hβγ
    apply P.root.injective
    have he := congrArg P.root h
    simpa only [P.root_reflectionPerm, P.reflection_apply_self, neg_inj] using he
  exact adjoint_conjugate_raising_distinctRoot_cartan_eq_zero P b R
    (weightCompanionRho P b O hclosed hmin R L.lift.val)
    (weightCompanionNRootPerm P b O hclosed hmin R L.lift) hn L.simple j
    (P.reflectionPerm β β) hne

end Atlas.Chevalley
