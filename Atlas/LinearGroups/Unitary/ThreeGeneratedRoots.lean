import Atlas.LinearGroups.Unitary.ThreeGeneratedMatrices

/-! Actual root-group inclusion in the transvection-generated SU₃ subgroup.
The base-field torus choice makes the necessary q>2 hypothesis explicit. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

private theorem mapped_inverse_of_right_inverse {G M : Type*} [Group G] [Monoid M]
    (f : G →* M) (g : G) (A : M) (hA : f g * A = 1) : f g⁻¹ = A := by
  calc
    f g⁻¹ = f g⁻¹ * (f g * A) := by rw [hA, mul_one]
    _ = A := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- Normality in the actual SU₃ gives every needed torus/root commutator. -/
theorem three_torus_commutator_mem_generated (hdeg : Module.finrank F K = 2)
    (a b : K) (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (t : K) (ht : t ≠ 0) (hfix : conjugation F K t = t)
    (c d : K) (hcd : rootThreeCondition (F := F) c d) :
    torusThreeMatrix t * rootThreeMatrix (F := F) c d * torusThreeMatrix t⁻¹ *
      rootThreeMatrix (F := F) (-c) (-d-c*conjugation F K c) ∈
        threeGeneratedMatrices hdeg a b ha := by
  let f := threeWittHom hdeg a b ha
  let H := transvectionGenerated hdeg (n := 3)
  obtain ⟨T, hT, hTe⟩ := torusThree_mem_generatedMatrices hdeg a b ha hb t ht hfix
  let R := rootThreeUnitary hdeg a b ha hb c d hcd
  have hRe : f R = rootThreeMatrix (F := F) c d := threeWittHom_root hdeg a b ha hb c d hcd
  have hTi : f T⁻¹ = torusThreeMatrix t⁻¹ := by
    apply mapped_inverse_of_right_inverse f T
    rw [show f T = torusThreeMatrix t from hTe, torusThreeMatrix_inverse t ht]
  have hRi : f R⁻¹ = rootThreeMatrix (F := F) (-c) (-d-c*conjugation F K c) := by
    apply mapped_inverse_of_right_inverse f R
    rw [hRe, rootThreeMatrix_inverse]
  have hconj : R * T⁻¹ * R⁻¹ ∈ H :=
    (inferInstance : H.Normal).conj_mem T⁻¹ (H.inv_mem hT) R
  refine ⟨T * (R * T⁻¹ * R⁻¹), H.mul_mem hT hconj, ?_⟩
  change f (T * (R * T⁻¹ * R⁻¹)) = _
  rw [map_mul, map_mul, map_mul, show f T = torusThreeMatrix t from hTe, hRe, hTi, hRi]
  simp only [mul_assoc]

/-- The entire actual positive root group lies in the transvection-generated
subgroup when q>2. The nonsimple binary rank-three case is deliberately excluded. -/
theorem rootThree_mem_generatedMatrices (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (c d : K) (hcd : rootThreeCondition (F := F) c d) :
    rootThreeMatrix (F := F) c d ∈ threeGeneratedMatrices hdeg a b ha := by
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨u, hu1⟩ := exists_ne (1 : Fˣ)
  let t := algebraMap F K (u : F)
  have ht : t ≠ 0 := (map_ne_zero _).mpr u.ne_zero
  have ht1 : t ≠ 1 := by
    intro h
    apply hu1
    apply Units.ext
    exact (algebraMap F K).injective (h.trans (map_one _).symm)
  have hfix : conjugation F K t = t := conjugation_base F K _
  exact rootThree_mem_of_center_commutators hdeg (threeGeneratedMatrices hdeg a b ha)
    (rootThree_center_mem_generatedMatrices hdeg a b ha hb) t ht ht1 hfix
    (three_torus_commutator_mem_generated hdeg a b ha hb t ht hfix) c d hcd

/-- The full K-unit torus also belongs to the actual generated subgroup image. -/
theorem fullTorus_mem_generatedMatrices (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (t : K) (ht : t ≠ 0) :
    fullTorusThreeMatrix (F := F) t ∈ threeGeneratedMatrices hdeg a b ha := by
  obtain ⟨z, hz, htrace⟩ := exists_nonzero_trace_zero hdeg
  have htrace' : -z + conjugation F K (-z) = 0 := by
    rw [map_neg]
    linear_combination -htrace
  exact fullTorus_mem_of_root_longWeyl hdeg (threeGeneratedMatrices hdeg a b ha)
    (rootThree_mem_generatedMatrices hdeg hq a b ha hb) z hz htrace
    (longWeyl_mem_generatedMatrices hdeg a b ha hb z hz htrace)
    (longWeyl_mem_generatedMatrices hdeg a b ha hb (-z) (neg_ne_zero.mpr hz) htrace') t ht
end Atlas.Unitary
