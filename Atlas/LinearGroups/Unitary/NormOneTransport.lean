import Atlas.LinearGroups.Unitary.Transvections

/-! Explicit unitary transport of norm-one vectors, including characteristic two.
The rank-one maps need not be special unitary; no generation theorem is used. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : ℕ}

/-- The general rank-one preservation identity, without an isotropy hypothesis. -/
theorem rankOne_preserves (hdeg : Module.finrank F K = 2)
    (v : Fin n → K) (a : K)
    (ha : a + conjugation F K a + a * conjugation F K a * hermitian F K v v = 0)
    (x y : Fin n → K) :
    hermitian F K (transvectionMatrix (F := F) v a *ᵥ x)
      (transvectionMatrix (F := F) v a *ᵥ y) = hermitian F K x y := by
  rw [transvectionMatrix_apply, transvectionMatrix_apply]
  simp only [hermitian_add_left, hermitian_add_right, hermitian_smul_left,
    hermitian_smul_right, map_mul, hermitian_symmetry hdeg]
  linear_combination hermitian F K x v * hermitian F K v y * ha

private theorem hermitian_sub_left' (v w z : Fin n → K) :
    hermitian F K (v - w) z = hermitian F K v z - hermitian F K w z := by
  have hn : -w = (-1 : K) • w := by simp
  rw [sub_eq_add_neg, hermitian_add_left, hn, hermitian_smul_left]
  ring
private theorem hermitian_sub_right' (v w z : Fin n → K) :
    hermitian F K v (w - z) = hermitian F K v w - hermitian F K v z := by
  have hn : -z = (-1 : K) • z := by simp
  rw [sub_eq_add_neg, hermitian_add_right, hn, hermitian_smul_right]
  simp [sub_eq_add_neg]

/-- A single explicit rank-one unitary transformation transports vectors when
its indicated denominator is nonzero. -/
theorem exists_unitary_map_of_pairing_ne_one (hdeg : Module.finrank F K = 2)
    (v w : Fin n → K) (hv : hermitian F K v v = 1) (hw : hermitian F K w w = 1)
    (hvw : hermitian F K v w ≠ 1) :
    ∃ g : U F K n hdeg, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = w := by
  let t := hermitian F K v w - 1
  have ht : t ≠ 0 := sub_ne_zero.mpr hvw
  have hbt : conjugation F K t ≠ 0 := (map_ne_zero (conjugation F K)).mpr ht
  have hd : hermitian F K (w - v) (w - v) = -t - conjugation F K t := by
    dsimp [t]
    rw [hermitian_sub_left', hermitian_sub_right', hermitian_sub_right', hv, hw,
      ← hermitian_symmetry hdeg v w]
    simp only [map_sub, map_one]
    ring
  have ha : t⁻¹ + conjugation F K t⁻¹ +
      t⁻¹ * conjugation F K t⁻¹ * hermitian F K (w - v) (w - v) = 0 := by
    rw [hd, map_inv₀]
    field_simp
    ring
  refine ⟨⟨transvectionMatrix (F := F) (w - v) t⁻¹,
    (mem_u_iff_preserves_hermitian hdeg _).mpr (rankOne_preserves hdeg _ _ ha)⟩, ?_⟩
  change transvectionMatrix (F := F) (w - v) t⁻¹ *ᵥ v = w
  rw [transvectionMatrix_apply, hermitian_sub_right', hv]
  change v + (t⁻¹ * t) • (w - v) = w
  rw [inv_mul_cancel₀ ht, one_smul]
  module

/-- Nontrivial norm-one scalars exist even over the two-element base field. -/
theorem exists_nontrivial_normOne_scalar (hdeg : Module.finrank F K = 2) :
    ∃ c : K, c * conjugation F K c = 1 ∧ c ≠ 1 := by
  have hex : ∃ t : K, conjugation F K t ≠ t := by
    by_contra! h
    apply conjugation_ne_one hdeg
    ext x
    exact h x
  obtain ⟨t, ht⟩ := hex
  have ht0 : t ≠ 0 := by rintro rfl; exact ht (map_zero _)
  have hbt : conjugation F K t ≠ 0 := (map_ne_zero (conjugation F K)).mpr ht0
  refine ⟨t / conjugation F K t, ?_, ?_⟩
  · rw [map_div₀, conjugation_conjugation hdeg]
    field_simp
  · intro h
    apply ht
    exact ((div_eq_one_iff_eq hbt).mp h).symm

/-- The actual retained unitary matrix group is transitive on norm-one vectors. -/
theorem exists_unitary_map (hdeg : Module.finrank F K = 2)
    (v w : Fin n → K) (hv : hermitian F K v v = 1) (hw : hermitian F K w w = 1) :
    ∃ g : U F K n hdeg, (g : Matrix (Fin n) (Fin n) K) *ᵥ v = w := by
  by_cases hvw : hermitian F K v w = 1
  · obtain ⟨c, hc, hc1⟩ := exists_nontrivial_normOne_scalar hdeg
    have hcw : hermitian F K (c • w) (c • w) = 1 := by
      rw [hermitian_smul_left, hermitian_smul_right, hw, mul_one, hc]
    have hv_cw : hermitian F K v (c • w) ≠ 1 := by
      rw [hermitian_smul_right, hvw, mul_one]
      intro h
      apply hc1
      have hh := congrArg (conjugation F K) h
      simpa only [conjugation_conjugation hdeg, map_one] using hh
    have hcw_w : hermitian F K (c • w) w ≠ 1 := by
      simpa only [hermitian_smul_left, hw, mul_one] using hc1
    obtain ⟨g, hg⟩ := exists_unitary_map_of_pairing_ne_one hdeg v (c • w) hv hcw hv_cw
    obtain ⟨k, hk⟩ := exists_unitary_map_of_pairing_ne_one hdeg (c • w) w hcw hw hcw_w
    refine ⟨k * g, ?_⟩
    change ((k : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)) *ᵥ v = w
    rw [← mulVec_mulVec, hg, hk]
  · exact exists_unitary_map_of_pairing_ne_one hdeg v w hv hw hvw
end Atlas.Unitary
