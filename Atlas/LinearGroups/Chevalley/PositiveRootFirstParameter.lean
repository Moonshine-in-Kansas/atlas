import Atlas.LinearAlgebra.HeightDepthList
import Atlas.LinearGroups.Chevalley.PositiveRootAdjointDepth
import Atlas.LinearGroups.Chevalley.RootLiftCartanOffDiagonal

/-! Recovery of the first parameter in a fixed list of positive-root families.
The first root occurs only once and has minimal height. No collection, canonical
root-family choice, full coordinate uniqueness or global projection kernel is assumed. -/

noncomputable section
open scoped Matrix
universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule

variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R] [Nontrivial R]
  (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
      μ (corootElement P i) = 1)
  (L : ∀ β : {β : ι // b.IsPos β}, WeightCompanionRootLift P b O hclosed hmin R β.val)

/-- An actual witnessed root factor on the adjoint summand. -/
def positiveRootLiftAdjointFactor (β : {β : ι // b.IsPos β}) (t : R) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  (weightCompanionRho P b O hclosed hmin R
    (weightCompanionRootLiftHom P b O hclosed hmin R (L β) (Multiplicative.ofAdd t))).val.val

/-- The literal ordered product in the existing companion group, for fixed
witnesses. Its image is not asserted to be a subgroup here. -/
def positiveRootLiftProduct (l : List {β : ι // b.IsPos β})
    (s : {β : ι // b.IsPos β} → R) : WeightCompanion P b O hclosed hmin R :=
  (l.map (fun β => weightCompanionRootLiftHom P b O hclosed hmin R
    (L β) (Multiplicative.ofAdd (s β)))).prod

theorem positiveRootLiftProduct_matrix (l : List {β : ι // b.IsPos β})
    (s : {β : ι // b.IsPos β} → R) :
    (weightCompanionRho P b O hclosed hmin R
      (positiveRootLiftProduct P b R O hclosed hmin L l s)).val.val =
      (l.map (fun β => positiveRootLiftAdjointFactor P b R O hclosed hmin L β (s β))).prod := by
  induction l with
  | nil =>
    simp [positiveRootLiftProduct]
  | cons β l ih =>
    change (weightCompanionRho P b O hclosed hmin R
      (weightCompanionRootLiftHom P b O hclosed hmin R (L β) (Multiplicative.ofAdd (s β)) *
        positiveRootLiftProduct P b R O hclosed hmin L l s)).val.val = _
    rw [map_mul]
    change positiveRootLiftAdjointFactor P b R O hclosed hmin L β (s β) *
      (weightCompanionRho P b O hclosed hmin R
        (positiveRootLiftProduct P b R O hclosed hmin L l s)).val.val =
      positiveRootLiftAdjointFactor P b R O hclosed hmin L β (s β) *
        (l.map (fun γ => positiveRootLiftAdjointFactor P b R O hclosed hmin L γ (s γ))).prod
    rw [ih]

theorem positiveRootLiftAdjointFactor_depth (β : {β : ι // b.IsPos β}) (t : R) :
    Atlas.Matrix.HeightAtLeast (geckHeight P b) (b.height β.val)
      (positiveRootLiftAdjointFactor P b R O hclosed hmin L β t - 1) :=
  weightCompanionRho_rootLiftHom_sub_one_heightAtLeast P b R O hclosed hmin
    β.property (L β) (Multiplicative.ofAdd t)

/-- The Cartan/negative-beta entry of the beta factor reads its first coefficient. -/
theorem positiveRootLiftAdjointFactor_own_firstEntry
    (β : {β : ι // b.IsPos β}) (t : R) (j : b.support) :
    (positiveRootLiftAdjointFactor P b R O hclosed hmin L β t - 1)
        (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) =
      t • adjointConjugateRaisingDivided P b R
        (weightCompanionRho P b O hclosed hmin R (L β).lift.val)
        (L β).simple 1 (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) := by
  apply weightCompanionRho_rootLiftHom_first_degree P b R O hclosed hmin
    β.property (L β) (Multiplicative.ofAdd t)
  change (0 : ℤ) = b.height (P.reflectionPerm β.val β.val) + b.height β.val
  have hneg := b.height_reflectionPerm_self β.val
  change b.height (P.reflectionPerm β.val β.val) = -b.height β.val at hneg
  rw [hneg]
  omega

/-- A different root of at least the first root's height contributes nothing
to that first root's Cartan/negative-root entry. -/
theorem positiveRootLiftAdjointFactor_distinct_firstEntry
    (β γ : {β : ι // b.IsPos β}) (hne : β ≠ γ)
    (hheight : b.height β.val ≤ b.height γ.val) (t : R) (j : b.support) :
    (positiveRootLiftAdjointFactor P b R O hclosed hmin L γ t - 1)
      (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) = 0 := by
  by_cases hh : b.height β.val = b.height γ.val
  · have he := weightCompanionRho_rootLiftHom_first_degree P b R O hclosed hmin
      γ.property (L γ) (Multiplicative.ofAdd t)
      (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) (by
        change (0 : ℤ) = b.height (P.reflectionPerm β.val β.val) + b.height γ.val
        have hneg := b.height_reflectionPerm_self β.val
        change b.height (P.reflectionPerm β.val β.val) = -b.height β.val at hneg
        rw [hneg]
        omega)
    have hlabels : β.val ≠ γ.val := fun h => hne (Subtype.ext h)
    have hz := weightCompanionRootLift_raising_distinctLabel_cartan_eq_zero
      P b R O hclosed hmin (L γ) hlabels j
    dsimp only at hz
    rw [rootVector_eq_single, Matrix.mulVec_single_one] at hz
    change ((weightCompanionRho P b O hclosed hmin R (L γ).lift.val).val.val *
      raisingOver P b R (L γ).simple *
      ((weightCompanionRho P b O hclosed hmin R (L γ).lift.val)⁻¹).val.val)
        (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) = 0 at hz
    rw [adjointConjugateRaisingDivided_one] at he
    simpa only [positiveRootLiftAdjointFactor, toAdd_ofAdd, hz, smul_zero] using he
  · apply positiveRootLiftAdjointFactor_depth P b R O hclosed hmin L γ t
    change (0 : ℤ) < b.height (P.reflectionPerm β.val β.val) + b.height γ.val
    have hneg := b.height_reflectionPerm_self β.val
    change b.height (P.reflectionPerm β.val β.val) = -b.height β.val at hneg
    rw [hneg]
    omega

/-- The first Cartan/negative-root entry of an actual product is contributed
only by its first factor, if that root occurs once and has minimal height. -/
theorem positiveRootLiftProduct_first_cartan_entry
    (β : {β : ι // b.IsPos β}) (l : List {β : ι // b.IsPos β}) (hnot : β ∉ l)
    (hheight : ∀ γ ∈ l, b.height β.val ≤ b.height γ.val)
    (s : {β : ι // b.IsPos β} → R) (j : b.support) :
    ((weightCompanionRho P b O hclosed hmin R
      (positiveRootLiftProduct P b R O hclosed hmin L (β :: l) s)).val.val - 1)
        (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) =
      (positiveRootLiftAdjointFactor P b R O hclosed hmin L β (s β) - 1)
        (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) := by
  let f := fun γ => positiveRootLiftAdjointFactor P b R O hclosed hmin L γ (s γ)
  have hd : 0 < b.height β.val := b.isPos_iff.mp β.property
  have hf : ∀ γ ∈ β :: l,
      Atlas.Matrix.HeightAtLeast (geckHeight P b) (b.height β.val) (f γ - 1) := by
    intro γ hγ
    rcases List.mem_cons.mp hγ with hγβ | hγ
    · subst γ
      exact positiveRootLiftAdjointFactor_depth P b R O hclosed hmin L β (s β)
    · exact (positiveRootLiftAdjointFactor_depth P b R O hclosed hmin L γ (s γ)).mono
        (hheight γ hγ)
  have he := Atlas.Matrix.HeightAtLeast.list_prod_sub_one_first_degree hd f (β :: l) hf
    (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) (by
      change (0 : ℤ) = b.height (P.reflectionPerm β.val β.val) + b.height β.val
      have hneg := b.height_reflectionPerm_self β.val
      change b.height (P.reflectionPerm β.val β.val) = -b.height β.val at hneg
      rw [hneg]
      omega)
  have htail : (l.map (fun γ => (f γ - 1)
      (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
    exact positiveRootLiftAdjointFactor_distinct_firstEntry P b R O hclosed hmin L
      β γ (fun h => hnot (h.symm ▸ hγ)) (hheight γ hγ) (s γ) j
  simp only [List.map_cons, List.sum_cons, htail, add_zero] at he
  rw [positiveRootLiftProduct_matrix]
  exact he

/-- Equality of the actual adjoint images of two products recovers their first
parameters. The first label is unique in the list and of minimal height; a
sorted list of distinct positive roots satisfies these hypotheses. -/
theorem positiveRootLiftProduct_first_parameter_of_adjoint_eq
    (β : {β : ι // b.IsPos β}) (l : List {β : ι // b.IsPos β}) (hnot : β ∉ l)
    (hheight : ∀ γ ∈ l, b.height β.val ≤ b.height γ.val)
    (s t : {β : ι // b.IsPos β} → R)
    (heq : weightCompanionRho P b O hclosed hmin R
        (positiveRootLiftProduct P b R O hclosed hmin L (β :: l) s) =
      weightCompanionRho P b O hclosed hmin R
        (positiveRootLiftProduct P b R O hclosed hmin L (β :: l) t)) : s β = t β := by
  let g := weightCompanionRho P b O hclosed hmin R (L β).lift.val
  let D := g.val.val * raisingOver P b R (L β).simple * (g⁻¹).val.val
  let v := D *ᵥ rootVector P b R (P.reflectionPerm β.val β.val)
  have hcartan : ∀ j : b.support, (s β - t β) • v (Sum.inl j) = 0 := by
    intro j
    have hs := positiveRootLiftProduct_first_cartan_entry P b R O hclosed hmin L
      β l hnot hheight s j
    have ht := positiveRootLiftProduct_first_cartan_entry P b R O hclosed hmin L
      β l hnot hheight t j
    have hentry := congrArg (fun a : Adjoint P b R =>
      (a.val.val - 1) (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val))) heq
    simp only [hs, ht, positiveRootLiftAdjointFactor_own_firstEntry,
      adjointConjugateRaisingDivided_one] at hentry
    change s β * D (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) =
      t β * D (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) at hentry
    change (s β - t β) * (D *ᵥ rootVector P b R (P.reflectionPerm β.val β.val)) (Sum.inl j) = 0
    rw [rootVector_eq_single, Matrix.mulVec_single_one]
    change (s β - t β) * D (Sum.inl j) (Sum.inr (P.reflectionPerm β.val β.val)) = 0
    rw [sub_mul]
    exact sub_eq_zero.mpr hentry
  have hroot : ∀ γ : ι, v (Sum.inr γ) = 0 := by
    intro γ
    obtain ⟨a, ha⟩ := weightCompanionRootLift_raising_negativeColumn P b R O hclosed hmin (L β)
    change v = a.val • (g.val.val *ᵥ cartanVector P b R (L β).simple) at ha
    have hc := weightCompanionExtendedWeyl_le_cartanBlock P b R O hclosed hmin (L β).lift.property
    have hz : g.val.val (Sum.inr γ) (Sum.inl (L β).simple) = 0 := hc.1 γ (L β).simple
    have he := congrFun ha (Sum.inr γ)
    simp only [Pi.smul_apply, cartanVector_eq_single, Matrix.mulVec_single_one] at he
    change v (Sum.inr γ) = a.val • g.val.val (Sum.inr γ) (Sum.inl (L β).simple) at he
    simpa only [hz, smul_zero] using he
  have hv : (s β - t β) • v = 0 := by
    ext row
    cases row with
    | inl j => exact hcartan j
    | inr γ => simp only [Pi.smul_apply, hroot γ, smul_zero, Pi.zero_apply]
  have hzero := (weightCompanionRootLift_raising_negativeColumn_smul_eq_zero_iff
    P b R O hclosed hmin (L β) (s β - t β)).mp hv
  exact sub_eq_zero.mp hzero

end Atlas.Chevalley
