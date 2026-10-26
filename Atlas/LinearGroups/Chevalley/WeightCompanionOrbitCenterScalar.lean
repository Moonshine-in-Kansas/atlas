import Atlas.LinearGroups.Chevalley.WeightCompanionFiniteCenter

/-! A central companion element acts by a scalar on each actual reflection-
transitive weight block. This uses the literal torus and its weight character,
not irreducibility of a representation or faithfulness of a Clifford algebra. -/
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
  (K : Type*) [Field K] [Finite K] [Fintype κ]

theorem weightCompanion_center_minuscule_scalar
    (hdiamond : SimpleDiamondProducts P b) (a : κ) (μ₀ : WeightOrbit P (O a))
    (htrans : ∀ μ : WeightOrbit P (O a), Relation.ReflTransGen
      (fun ν ξ => ∃ i : ι, weightReflection P i ν = ξ) μ₀.val μ.val)
    (g : WeightCompanion P b O hc hm K)
    (hg : g ∈ Subgroup.center (WeightCompanion P b O hc hm K)) :
    ∃ c : Kˣ, (g.val.2 a).val = (c : K) • (1 : Matrix _ _ K) := by
  have ht := weightCompanion_center_le_torus_finiteField P b O hc hm K hdiamond hg
  rw [weightCompanionTorusSubgroup_eq_range] at ht
  obtain ⟨t,rfl⟩ := ht
  have hk := weightCompanion_center_le_rhoKernel_finiteField P b O hc hm K hdiamond hg
  change weightCompanionRho P b O hc hm K
    (weightCompanionTorusParameters P b O hc hm K t) = 1 at hk
  rw [weightCompanionRho_torusParameters] at hk
  have hr := (adjointTorusParameters_eq_one_iff_character P K b t).mp hk
  let f := weightTorusCharacterHom P b K t
  have hstep (i : ι) (μ : WeightLattice P) :
      f (Multiplicative.ofAdd (weightReflection P i μ)) = f (Multiplicative.ofAdd μ) := by
    rw [weightReflection_apply, ofAdd_sub,
      ofAdd_zsmul, map_div, map_zpow]
    rw [show f (Multiplicative.ofAdd (rootWeight P i)) = 1 from hr i,
      one_zpow, div_one]
  have hpath {μ ν : WeightLattice P}
      (h : Relation.ReflTransGen (fun ξ ζ => ∃ i : ι, weightReflection P i ξ = ζ) μ ν) :
      f (Multiplicative.ofAdd ν) = f (Multiplicative.ofAdd μ) := by
    induction h with
    | refl => rfl
    | @tail ν ξ _ hs ih =>
      obtain ⟨i,hi⟩ := hs
      rw [← hi]
      exact (hstep i ν).trans ih
  let c : Kˣ := f (Multiplicative.ofAdd μ₀.val)
  refine ⟨c, ?_⟩
  change ((weightCompanionTorusProduct P b O hc hm K Finset.univ t).val.2 a).val = _
  rw [weightCompanionTorusProduct_minuscule]
  have hb (i : b.support) : corootBasis P b i = corootElement P i.val := by
    apply Subtype.ext
    exact b.flip.coe_toWeightBasisInt_apply i
  have hd (μ : WeightOrbit P (O a)) :
      (∏ i : b.support, ((t i) ^ μ.val (corootElement P i.val)).val) = (c : K) := by
    have hh := congrArg Units.val (hpath (htrans μ))
    simpa only [c, f, weightTorusCharacterHom, MonoidHom.coe_mk, OneHom.coe_mk,
      weightTorusCharacter, toAdd_ofAdd, map_prod, Units.coe_prod, hb] using hh
  have he : (fun μ : WeightOrbit P (O a) =>
      ∏ i ∈ (Finset.univ : Finset b.support), ((t i) ^ μ.val (corootElement P i.val)).val) =
      fun _ => (c : K) := by funext μ; simpa using hd μ
  rw [he]
  ext μ ν
  by_cases h : μ=ν <;> simp [Matrix.diagonal, Matrix.one_apply, h]

end Atlas.Chevalley
