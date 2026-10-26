import Atlas.LinearGroups.Chevalley.PositiveWitnessedNormalizerSigns

/-! Reduce n_i*x_i(t)*n by the sign of the actual inverse image of alpha_i.
This is an actual full-companion calculation, with no Bruhat or BN premise. -/
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
  (K : Type*) [Field K]

theorem weightCompanion_simple_X_N_mem_doubleCoset_of_positive
    (i : b.support) (n : weightCompanionExtendedWeylSubgroup P b O hc hm K)
    (hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm K n⁻¹ i.val))
    (t : K) :
    weightCompanionWeyl P b O hc hm K i 1 * weightCompanionX P b O hc hm K i t *
      n.val ∈ DoubleCoset.doubleCoset
        (weightCompanionWeyl P b O hc hm K i 1 * n.val)
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  have hp := weightCompanionN_conjugate_X_mem_positiveWitnessed
    P b O hc hm K n⁻¹ i hpos t
  have hp' : n.val⁻¹ * weightCompanionX P b O hc hm K i t * n.val ∈ B := by
    apply (show positiveWitnessedWeightCompanionSubgroup P b O hc hm K ≤ B from le_sup_left)
    simpa only [Subgroup.coe_inv,inv_inv] using hp
  apply DoubleCoset.mem_doubleCoset.mpr
  refine ⟨1,B.one_mem,n.val⁻¹ * weightCompanionX P b O hc hm K i t * n.val,hp',?_⟩
  group

/-- In the negative-sign case, every nonzero simple-root parameter drops to
the n-cell. The rank-one diagonal factor is a literal ring unit. -/
theorem weightCompanion_simple_X_N_mem_doubleCoset_of_negative_nonzero
    (i : b.support) (n : weightCompanionExtendedWeylSubgroup P b O hc hm K)
    (hneg : ¬ b.IsPos (weightCompanionNRootPermHom P b O hc hm K n⁻¹ i.val))
    (t : K) (ht : t ≠ 0) :
    weightCompanionWeyl P b O hc hm K i 1 * weightCompanionX P b O hc hm K i t *
      n.val ∈ DoubleCoset.doubleCoset n.val
        (positiveWitnessedTorusJoin P b O hc hm K)
        (positiveWitnessedTorusJoin P b O hc hm K) := by
  let B := positiveWitnessedTorusJoin P b O hc hm K
  let T := weightCompanionTorusSubgroup P b O hc hm K
  let s := weightCompanionWeyl P b O hc hm K i 1
  let r : K := (-t)⁻¹
  let a : Kˣ := -(Units.mk0 (-t) (neg_ne_zero.mpr ht))⁻¹
  have hleft : weightCompanionX P b O hc hm K i r *
      weightCompanionTorus P b O hc hm K i a ∈ B :=
    B.mul_mem (weightCompanionX_mem_positiveWitnessedTorusJoin P b O hc hm K i r)
      (weightCompanionTorus_mem_positiveWitnessedTorusJoin P b O hc hm K i a)
  have hy := weightCompanionN_conjugate_Y_mem_positiveWitnessed_of_negative
    P b O hc hm K n⁻¹ i hneg (-r)
  have hyB : n.val⁻¹ * weightCompanionY P b O hc hm K i (-r) * n.val ∈ B := by
    apply (show positiveWitnessedWeightCompanionSubgroup P b O hc hm K ≤ B from le_sup_left)
    simpa only [Subgroup.coe_inv,inv_inv] using hy
  have hsquare : s^2 ∈ T := by
    rw [show s^2 = weightCompanionTorus P b O hc hm K i (-1) from
      weightCompanionWeyl_one_sq P b O hc hm K i]
    exact Subgroup.subset_closure ⟨i,(-1 : Kˣ),rfl⟩
  have htconj : n.val⁻¹*s^2*n.val ∈ T :=
    (Subgroup.mem_normalizer_iff''.mp
      (weightCompanionExtendedWeylSubgroup_le_torusNormalizer
        P b O hc hm K n.property) (s^2)).mp hsquare
  have hright : (n.val⁻¹ * weightCompanionY P b O hc hm K i (-r) * n.val) *
      (n.val⁻¹*s^2*n.val) ∈ B :=
    B.mul_mem hyB ((show T ≤ B from le_sup_right) htconj)
  have hys : weightCompanionY P b O hc hm K i (-t) =
      weightCompanionX P b O hc hm K i r * weightCompanionTorus P b O hc hm K i a *
        s * weightCompanionX P b O hc hm K i r :=
    weightCompanionY_eq_rankOne_product_of_ne_zero P b O hc hm K i (-t) (neg_ne_zero.mpr ht)
  have hsx : s * weightCompanionX P b O hc hm K i t * s⁻¹ =
      weightCompanionY P b O hc hm K i (-t) :=
    weightCompanionWeyl_one_conjugate_X_same P b O hc hm K i t
  have hsxr : s * weightCompanionX P b O hc hm K i r * s⁻¹ =
      weightCompanionY P b O hc hm K i (-r) :=
    weightCompanionWeyl_one_conjugate_X_same P b O hc hm K i r
  apply DoubleCoset.mem_doubleCoset.mpr
  refine ⟨weightCompanionX P b O hc hm K i r * weightCompanionTorus P b O hc hm K i a,
    hleft,(n.val⁻¹ * weightCompanionY P b O hc hm K i (-r) * n.val) *
      (n.val⁻¹*s^2*n.val),hright,?_⟩
  change s * weightCompanionX P b O hc hm K i t * n.val = _
  calc
    s * weightCompanionX P b O hc hm K i t * n.val =
        weightCompanionY P b O hc hm K i (-t) * s * n.val := by rw [← hsx]; group
    _ = (weightCompanionX P b O hc hm K i r * weightCompanionTorus P b O hc hm K i a) *
        (s * weightCompanionX P b O hc hm K i r * s⁻¹) * s^2 * n.val := by rw [hys]; group
    _ = _ := by rw [hsxr]; group

theorem weightCompanion_simple_X_N_mem_doubleCosets
    (i : b.support) (n : weightCompanionExtendedWeylSubgroup P b O hc hm K) (t : K) :
    weightCompanionWeyl P b O hc hm K i 1 * weightCompanionX P b O hc hm K i t *
        n.val ∈ DoubleCoset.doubleCoset
          (weightCompanionWeyl P b O hc hm K i 1 * n.val)
          (positiveWitnessedTorusJoin P b O hc hm K)
          (positiveWitnessedTorusJoin P b O hc hm K) ∨
    weightCompanionWeyl P b O hc hm K i 1 * weightCompanionX P b O hc hm K i t *
        n.val ∈ DoubleCoset.doubleCoset n.val
          (positiveWitnessedTorusJoin P b O hc hm K)
          (positiveWitnessedTorusJoin P b O hc hm K) := by
  by_cases hpos : b.IsPos (weightCompanionNRootPermHom P b O hc hm K n⁻¹ i.val)
  · exact Or.inl (weightCompanion_simple_X_N_mem_doubleCoset_of_positive
      P b O hc hm K i n hpos t)
  · by_cases ht : t = 0
    · left
      subst t
      have hzero : weightCompanionX P b O hc hm K i 0 = 1 :=
        (weightCompanionXHom P b O hc hm K i).map_one
      rw [hzero,mul_one]
      exact DoubleCoset.mem_doubleCoset_self _ _ _
    · exact Or.inr (weightCompanion_simple_X_N_mem_doubleCoset_of_negative_nonzero
        P b O hc hm K i n hpos t ht)

end Atlas.Chevalley
