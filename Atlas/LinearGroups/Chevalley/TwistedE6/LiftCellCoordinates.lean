import Atlas.LinearGroups.Chevalley.PositiveRootWeylSubsetTransport
import Atlas.LinearGroups.Chevalley.PositiveRootSubsetFactorization
import Atlas.LinearGroups.Chevalley.RootData.PositiveRootInversionCardinality
import Mathlib.GroupTheory.DoubleCoset

/-! Unique coordinates for a literal cell using any actual normalizer lift.
This generalizes the existing chosen-lift proof by retaining its root-action
identity as an explicit input. It uses no whole-group order theorem. -/
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
  (w : P.weylGroupToPerm.range)
  (n : weightCompanionExtendedWeylSubgroup P b O hc hm R)

/-- Literal multiplication into the double coset; no counting premise. -/
def positiveWitnessedLiftCellParameterMap :
    positiveRootSubsetSubgroup P b O hc hm R (positiveRootInversionSubset P b w⁻¹) ×
      positiveWitnessedTorusJoin P b O hc hm R →
        ↥(DoubleCoset.doubleCoset n.val
          (positiveWitnessedTorusJoin P b O hc hm R) (positiveWitnessedTorusJoin P b O hc hm R)) :=
  fun p => ⟨p.1.val * n.val * p.2.val,
    DoubleCoset.mem_doubleCoset.mpr ⟨p.1.val,
      (show positiveWitnessedWeightCompanionSubgroup P b O hc hm R ≤
        positiveWitnessedTorusJoin P b O hc hm R from le_sup_left)
          (positiveRootSubsetSubgroup_le_witnessed P b O hc hm R _ p.1.property),
      p.2.val, p.2.property, rfl⟩⟩

theorem positiveWitnessedLiftCellParameterMap_injective
    (hdiamond : SimpleDiamondProducts P b)
    (hn : weightCompanionNRootPermHom P b O hc hm R n = w.val) :
    Function.Injective (positiveWitnessedLiftCellParameterMap P b O hc hm R w n) := by
  intro x y hxy
  let H := positiveRootSubsetSubgroup P b O hc hm R (positiveRootInversionSubset P b w⁻¹)
  let B := positiveWitnessedTorusJoin P b O hc hm R
  have he : x.1.val * n.val * x.2.val = y.1.val * n.val * y.2.val :=
    congrArg Subtype.val hxy
  let d := y.1.val⁻¹ * x.1.val
  have hd : d ∈ H := H.mul_mem (H.inv_mem y.1.property) x.1.property
  have hop : n.val⁻¹ * d * n.val ∈
      oppositePositiveWitnessedWeightCompanionSubgroup P b O hc hm R := by
    apply positiveRootInversionSubset_conjugate_le_opposite P b O hc hm R w n
      hn
    exact ⟨d, hd, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hec : n.val⁻¹ * d * n.val = y.2.val * x.2.val⁻¹ := by
    calc
      n.val⁻¹ * d * n.val =
        n.val⁻¹ * y.1.val⁻¹ * (x.1.val * n.val * x.2.val) * x.2.val⁻¹ := by
          dsimp only [d]; group
      _ = n.val⁻¹ * y.1.val⁻¹ * (y.1.val * n.val * y.2.val) * x.2.val⁻¹ := by rw [he]
      _ = y.2.val * x.2.val⁻¹ := by group
  have hb : n.val⁻¹ * d * n.val ∈ B := by
    rw [hec]
    exact B.mul_mem y.2.property (B.inv_mem x.2.property)
  have hc1 := oppositePositiveWitnessed_eq_one_of_mem_torusJoin
    P b O hc hm R hdiamond _ hop hb
  have hd1 : d = 1 := by
    calc
      d = n.val * (n.val⁻¹ * d * n.val) * n.val⁻¹ := by group
      _ = 1 := by rw [hc1]; group
  have he1 : x.1.val = y.1.val := by
    calc
      x.1.val = y.1.val * d := by dsimp only [d]; group
      _ = y.1.val := by rw [hd1, mul_one]
  have he2 : x.2.val = y.2.val := by
    apply mul_left_cancel (a := y.1.val * n.val)
    simpa only [he1] using he
  exact Prod.ext (Subtype.ext he1) (Subtype.ext he2)

/-- Absorb the noninversion factor and the torus into the right B coordinate.
Finiteness is used only in the already proved U-subset partition bijection. -/
theorem positiveWitnessedLiftCellParameterMap_surjective [Finite R]
    (hdiamond : SimpleDiamondProducts P b)
    (hn : weightCompanionNRootPermHom P b O hc hm R n = w.val) :
    Function.Surjective (positiveWitnessedLiftCellParameterMap P b O hc hm R w n) := by
  intro g
  let U := positiveWitnessedWeightCompanionSubgroup P b O hc hm R
  let T := weightCompanionTorusSubgroup P b O hc hm R
  let B := positiveWitnessedTorusJoin P b O hc hm R
  obtain ⟨a, ha, b', hb', hg⟩ := DoubleCoset.mem_doubleCoset.mp g.property
  have hprod : a ∈ (U : Set (WeightCompanion P b O hc hm R)) *
      (T : Set (WeightCompanion P b O hc hm R)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U T
      (weightCompanionTorus_le_positiveWitnessedNormalizer P b O hc hm R)]
    exact ha
  obtain ⟨u, hu, t, ht, hut⟩ := hprod
  obtain ⟨p, hp⟩ := (positiveRootSubsetMul_bijective_of_partition P b O hc hm R hdiamond
    (positiveRootInversionSubset P b w⁻¹) (positiveRootNoninversionSubset P b w⁻¹)
    (positiveRootConeClosed_inversionSubset P b w⁻¹)
    (positiveRootConeClosed_noninversionSubset P b w⁻¹)
    (positiveRootInversionSubset_disjoint P b w⁻¹)
    (positiveRootInversionSubset_union_noninversion P b w⁻¹)).surjective ⟨u, hu⟩
  have hup : p.1.val * p.2.val = u := congrArg Subtype.val hp
  have hun : n.val⁻¹ * p.2.val * n.val ∈ U := by
    apply positiveRootNoninversionSubset_conjugate_le_positive P b O hc hm R w n
      hn
    exact ⟨p.2.val, p.2.property,
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hnt : n.val⁻¹ * t * n.val ∈ T := by
    have hn := weightCompanionExtendedWeylSubgroup_le_torusNormalizer
      P b O hc hm R (show n.val⁻¹ ∈ weightCompanionExtendedWeylSubgroup P b O hc hm R from
        (weightCompanionExtendedWeylSubgroup P b O hc hm R).inv_mem n.property)
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hn t).mp ht
  let c := (n.val⁻¹ * p.2.val * n.val) * (n.val⁻¹ * t * n.val) * b'
  have hcB : c ∈ B := B.mul_mem
    (B.mul_mem ((show U ≤ B from le_sup_left) hun)
      ((show T ≤ B from le_sup_right) hnt)) hb'
  refine ⟨(p.1, ⟨c, hcB⟩), Subtype.ext ?_⟩
  change p.1.val * n.val * c = g.val
  rw [hg, ← hut, ← hup]
  dsimp only [c]
  group

/-- A set equivalence onto a single literal double cell, not a group equivalence. -/
def positiveWitnessedLiftCellParameterEquiv [Finite R]
    (hdiamond : SimpleDiamondProducts P b)
    (hn : weightCompanionNRootPermHom P b O hc hm R n = w.val) :
    positiveRootSubsetSubgroup P b O hc hm R (positiveRootInversionSubset P b w⁻¹) ×
      positiveWitnessedTorusJoin P b O hc hm R ≃
        ↥(DoubleCoset.doubleCoset n.val
          (positiveWitnessedTorusJoin P b O hc hm R) (positiveWitnessedTorusJoin P b O hc hm R)) :=
  Equiv.ofBijective (positiveWitnessedLiftCellParameterMap P b O hc hm R w n)
    ⟨positiveWitnessedLiftCellParameterMap_injective P b O hc hm R w n hdiamond hn,
      positiveWitnessedLiftCellParameterMap_surjective P b O hc hm R w n hdiamond hn⟩

end Atlas.Chevalley
