import Atlas.LinearGroups.Unitary.WittPair
import Atlas.LinearGroups.Unitary.Order
import Atlas.FieldTheory.FiniteQuadraticCounts
import Atlas.LinearGroups.SL2Order

/-! The concrete special-unitary plane compared with the existing SL₂ carrier. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped MatrixGroups
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Diagonal conjugation by diag(t,1), written entrywise. -/
def rankOneTwist (t : K) (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![A 0 0, t * A 0 1; t⁻¹ * A 1 0, A 1 1]

omit [Finite K] in
theorem rankOneTwist_det (t : K) (ht : t ≠ 0) (A : Matrix (Fin 2) (Fin 2) K) :
    (rankOneTwist t A).det = A.det := by
  simp only [rankOneTwist, det_fin_two, of_apply, cons_val_zero, cons_val_one,
    cons_val_fin_one]
  field_simp

omit [Finite K] in
theorem rankOneTwist_one (t : K) : rankOneTwist t 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rankOneTwist]

omit [Finite K] in
theorem rankOneTwist_mul (t : K) (ht : t ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) K) :
    rankOneTwist t (A * B) = rankOneTwist t A * rankOneTwist t B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneTwist, mul_apply, Fin.sum_univ_two] <;> field_simp

omit [Finite K] in
theorem rankOneTwist_injective (t : K) (ht : t ≠ 0) : Function.Injective (rankOneTwist t) := by
  intro A B h
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrArg (fun M => M 0 0) h
  · exact mul_left_cancel₀ ht (congrArg (fun M => M 0 1) h)
  · exact mul_left_cancel₀ (inv_ne_zero ht) (congrArg (fun M => M 1 0) h)
  · exact congrArg (fun M => M 1 1) h

/-- A trace-zero diagonal twist converts actual determinant-one base-field
matrices into isometries of the hyperbolic Hermitian plane. -/
theorem rankOneTwist_preserves (t : K) (ht : t ≠ 0)
    (htrace : t + conjugation F K t = 0) (g : SL(2,F)) (x y : Fin 2 → K) :
    hyperbolicPlaneForm (F := F)
      (rankOneTwist t (g.val.map (algebraMap F K)) *ᵥ x)
      (rankOneTwist t (g.val.map (algebraMap F K)) *ᵥ y) =
      hyperbolicPlaneForm (F := F) x y := by
  have hs : conjugation F K t = -t := by linear_combination htrace
  have hd : (algebraMap F K (g.val 0 0)) * algebraMap F K (g.val 1 1) -
      algebraMap F K (g.val 0 1) * algebraMap F K (g.val 1 0) = 1 := by
    have hd := g.prop
    rw [det_fin_two] at hd
    have h := congrArg (algebraMap F K) hd
    simpa only [map_sub, map_mul, map_one] using h
  simp only [hyperbolicPlaneForm, mulVec, dotProduct, Fin.sum_univ_two,
    rankOneTwist, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one,
    Matrix.map_apply, map_add, map_mul, map_inv₀, conjugation_base, hs, inv_neg]
  field_simp
  linear_combination t *
    (x 0 * conjugation F K (y 1) + x 1 * conjugation F K (y 0)) * hd

private theorem witt_det_unit (a b : K) (ha : a * conjugation F K a = -1) :
    IsUnit (wittPlaneMatrix a b).det := by
  rw [wittPlaneMatrix_det]
  apply isUnit_iff_ne_zero.mpr
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  exact neg_ne_zero.mpr ha0

/-- The explicit scalar-extension and change-of-basis matrix. -/
def rankOneMatrix (a b t : K) (g : SL(2,F)) : Matrix (Fin 2) (Fin 2) K :=
  wittPlaneMatrix a b * rankOneTwist t (g.val.map (algebraMap F K)) * (wittPlaneMatrix a b)⁻¹

theorem rankOneMatrix_det (a b t : K) (ha : a * conjugation F K a = -1)
    (ht : t ≠ 0) (g : SL(2,F)) : (rankOneMatrix a b t g).det = 1 := by
  have hP := witt_det_unit a b ha
  have hg : (g.val.map (algebraMap F K)).det = 1 := by
    exact ((algebraMap F K).map_det g.val).symm.trans (by rw [g.prop, map_one])
  simp only [rankOneMatrix, det_mul, rankOneTwist_det t ht, hg, mul_one, det_nonsing_inv, Ring.inverse_eq_inv]
  exact mul_inv_cancel₀ (isUnit_iff_ne_zero.mp hP)

theorem rankOneMatrix_preserves (a b t : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (ht : t ≠ 0) (htrace : t + conjugation F K t = 0)
    (g : SL(2,F)) (x y : Fin 2 → K) :
    hermitian F K (rankOneMatrix a b t g *ᵥ x) (rankOneMatrix a b t g *ᵥ y) =
      hermitian F K x y := by
  let P := wittPlaneMatrix a b
  have hP := witt_det_unit a b ha
  have hx : P *ᵥ (P⁻¹ *ᵥ x) = x := by rw [mulVec_mulVec, mul_nonsing_inv P hP, one_mulVec]
  have hy : P *ᵥ (P⁻¹ *ᵥ y) = y := by rw [mulVec_mulVec, mul_nonsing_inv P hP, one_mulVec]
  simp only [rankOneMatrix, ← mulVec_mulVec]
  rw [wittPlaneMatrix_preserves a b ha hb, rankOneTwist_preserves t ht htrace]
  exact (wittPlaneMatrix_preserves a b ha hb (P⁻¹ *ᵥ x) (P⁻¹ *ᵥ y)).symm.trans
    (congrArg₂ (hermitian F K) hx hy)


/-- An explicit homomorphism from the existing SL₂(F) to the retained SU₂(K/F). -/
def rankOneHom (hdeg : Module.finrank F K = 2) (a b t : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (ht : t ≠ 0) (htrace : t + conjugation F K t = 0) :
    SL(2,F) →* SU F K 2 hdeg where
  toFun g := ⟨rankOneMatrix a b t g,
    (mem_u_iff_preserves_hermitian hdeg _).mpr (rankOneMatrix_preserves a b t ha hb ht htrace g),
    rankOneMatrix_det a b t ha ht g⟩
  map_one' := by
    apply Subtype.ext
    change wittPlaneMatrix a b * rankOneTwist t ((1 : Matrix (Fin 2) (Fin 2) F).map
      (algebraMap F K)) * (wittPlaneMatrix a b)⁻¹ = 1
    rw [Matrix.map_one, rankOneTwist_one, mul_one, mul_nonsing_inv _ (witt_det_unit a b ha)] <;> simp
  map_mul' g h := by
    apply Subtype.ext
    change wittPlaneMatrix a b * rankOneTwist t ((g.val * h.val).map (algebraMap F K)) *
      (wittPlaneMatrix a b)⁻¹ = _
    rw [Matrix.map_mul, rankOneTwist_mul t ht]
    change _ = (wittPlaneMatrix a b * rankOneTwist t (g.val.map (algebraMap F K)) *
      (wittPlaneMatrix a b)⁻¹) *
      (wittPlaneMatrix a b * rankOneTwist t (h.val.map (algebraMap F K)) *
      (wittPlaneMatrix a b)⁻¹)
    simp only [mul_assoc, ← mul_assoc (wittPlaneMatrix a b)⁻¹ (wittPlaneMatrix a b),
      nonsing_inv_mul _ (witt_det_unit a b ha), one_mul]

theorem rankOneHom_injective (hdeg : Module.finrank F K = 2) (a b t : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (ht : t ≠ 0) (htrace : t + conjugation F K t = 0) :
    Function.Injective (rankOneHom hdeg a b t ha hb ht htrace) := by
  intro g h hgh
  have hmat := congrArg (fun z : SU F K 2 hdeg =>
    (wittPlaneMatrix a b)⁻¹ * z.val * wittPlaneMatrix a b) hgh
  change (wittPlaneMatrix a b)⁻¹ * (wittPlaneMatrix a b *
    rankOneTwist t (g.val.map (algebraMap F K)) * (wittPlaneMatrix a b)⁻¹) *
    wittPlaneMatrix a b = (wittPlaneMatrix a b)⁻¹ * (wittPlaneMatrix a b *
    rankOneTwist t (h.val.map (algebraMap F K)) * (wittPlaneMatrix a b)⁻¹) *
    wittPlaneMatrix a b at hmat
  have hP := witt_det_unit a b ha
  simp only [mul_assoc, ← mul_assoc (wittPlaneMatrix a b)⁻¹ (wittPlaneMatrix a b),
    nonsing_inv_mul _ hP, one_mul, mul_one] at hmat
  have he := rankOneTwist_injective t ht hmat
  apply Subtype.ext
  ext i j
  exact (algebraMap F K).injective (congrArg (fun M => M i j) he)

/-- Surjectivity of the constructed embedding uses already independent orders
of these actual carriers; no abstract recognition theorem is involved. -/
theorem rankOneHom_bijective (hdeg : Module.finrank F K = 2) (a b t : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (ht : t ≠ 0) (htrace : t + conjugation F K t = 0) :
    Function.Bijective (rankOneHom hdeg a b t ha hb ht htrace) := by
  have hc : Nat.card SL(2,F) = Nat.card (SU F K 2 hdeg) := by
    rw [Atlas.card_sl_two, card_su hdeg 2 (by decide)]
    norm_num [orderSU, orderFactor, Finset.prod_range_succ, Finset.sum_range_succ]
  let := Fintype.ofFinite SL(2,F)
  let := Fintype.ofFinite (SU F K 2 hdeg)
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨rankOneHom_injective hdeg a b t ha hb ht htrace, by
      simpa only [Nat.card_eq_fintype_card] using hc⟩

/-- The actual rank-one special unitary/special linear comparison, over every
finite base field, including q=2 and q=3. -/
def specialUnitaryTwoEquiv (hdeg : Module.finrank F K = 2) : SL(2,F) ≃* SU F K 2 hdeg := by
  apply Classical.choice
  obtain ⟨a, b, ha, hb⟩ := exists_witt_parameters hdeg
  obtain ⟨t, ht, htrace⟩ := exists_nonzero_trace_zero hdeg
  exact ⟨MulEquiv.ofBijective (rankOneHom hdeg a b t ha hb ht htrace)
    (rankOneHom_bijective hdeg a b t ha hb ht htrace)⟩
end Atlas.Unitary
