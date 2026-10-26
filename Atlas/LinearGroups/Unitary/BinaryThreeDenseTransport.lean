import Atlas.LinearGroups.Unitary.BinaryFourBridge
import Atlas.LinearGroups.Unitary.BinaryField
import Atlas.LinearGroups.Unitary.BlockEmbeddings

/-! A diagonal conjugate of the four-transvection Fourier bridge reduces a
fully supported binary three-dimensional complement vector. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable [CharP K 2]

private def denseDiagonal (hdeg : Module.finrank F K = 2) (hq : Nat.card F = 2)
    (v : Fin 3 → K) (hv : ∀ i, v i ≠ 0) : SU F K 4 hdeg := by
  let d : Fin 4 → K := Fin.cons (v 0 * v 1 * v 2)⁻¹ v
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    refine Fin.cases ?_ (fun j => hv j) i
    exact inv_ne_zero (mul_ne_zero (mul_ne_zero (hv 0) (hv 1)) (hv 2))
  refine ⟨Matrix.diagonal d, ?_, ?_⟩
  · apply (mem_u_iff_preserves_hermitian hdeg _).mpr
    intro x y
    simp only [hermitian, mulVec_diagonal, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    calc
      d i * x i * (conjugation F K (d i) * conjugation F K (y i)) =
          (d i * conjugation F K (d i)) * (x i * conjugation F K (y i)) := by ring
      _ = _ := by rw [binary_nonzero_norm hdeg hq (d i) (hd i), one_mul]
  · change (Matrix.diagonal d).det = 1
    rw [det_diagonal]
    simp [d, Fin.prod_univ_succ, mul_assoc, hv]

/-- The binary SU₃ Fourier move is available inside the actual generated SU₄,
after conjugating by determinant-corrected diagonal scalars. -/
theorem binary_dense_complement_transport (hdeg : Module.finrank F K = 2)
    (hq : Nat.card F = 2) (v : Fin 3 → K) (hv : ∀ i, v i ≠ 0) :
    ∃ g : SU F K 3 hdeg, extendSpecialHom hdeg g ∈ transvectionGenerated hdeg ∧
      g.val *ᵥ v = Pi.single 0 (v 0) := by
  classical
  obtain ⟨c,hc⟩ := exists_binary_primitive hdeg hq
  let D := denseDiagonal hdeg hq v hv
  let B := binaryBridgeElement hdeg hq c hc
  let G := D * B * D⁻¹
  have hg : G ∈ transvectionGenerated hdeg :=
    (inferInstance : (transvectionGenerated hdeg (n := 4)).Normal).conj_mem B (binaryBridgeElement_generated hdeg hq c hc) D
  have he (x : Fin 4 → K) : G.val *ᵥ (D.val *ᵥ x) = D.val *ᵥ (B.val *ᵥ x) := by
    change (D.val * B.val * (D⁻¹).val) *ᵥ (D.val *ᵥ x) = _
    simp only [mulVec_mulVec, mul_assoc]
    rw [show (D⁻¹).val * D.val = 1 from congrArg Subtype.val (inv_mul_cancel D), mul_one]
  have hd (x : Fin 4 → K) : D.val *ᵥ x =
      fun i => (Fin.cons ((v 0*v 1*v 2)⁻¹ : K) v : Fin 4 → K) i * x i := by
    change Matrix.diagonal (Fin.cons ((v 0*v 1*v 2)⁻¹ : K) v) *ᵥ x = _
    ext i
    exact mulVec_diagonal _ _ i
  have hBfix : B.val *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [show B.val = extendMatrix (binaryFourierThree c) from binaryBridgeElement_matrix hdeg hq c hc]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Matrix.mulVec_single_one, Matrix.col, extendMatrix, Pi.single_apply]
  have hfix : G.val *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    have h := he ((v 0*v 1*v 2) • Pi.single 0 1)
    have hd0 : D.val *ᵥ ((v 0*v 1*v 2) • Pi.single 0 1) = Pi.single 0 1 := by
      rw [hd]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [hv]; field_simp [hv]
      · simp [Pi.single_apply]
    rw [hd0, mulVec_smul, hBfix, hd0] at h
    exact h
  have hG : G ∈ firstSpecialStabilizer (n := 3) hdeg := by
    change G • coordinateUnit (F := F) (K := K) 0 = coordinateUnit 0
    apply Subtype.ext
    exact hfix
  let g := firstSpecialStabilizerEquiv hdeg ⟨G,hG⟩
  have hExt : extendSpecialHom hdeg g = G :=
    congrArg Subtype.val ((firstSpecialStabilizerEquiv hdeg).symm_apply_apply ⟨G,hG⟩)
  refine ⟨g, hExt ▸ hg, ?_⟩
  have h := he (Fin.cons 0 (fun _ => 1))
  have hdv : D.val *ᵥ Fin.cons 0 (fun _ => 1) = Fin.cons 0 v := by
    rw [hd]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hBv : B.val *ᵥ Fin.cons 0 (fun _ => 1) = Fin.cons 0 (Pi.single 0 1) := by
    rw [show B.val = extendMatrix (binaryFourierThree c) from binaryBridgeElement_matrix hdeg hq c hc,
      extendMatrix_mulVec]
    congr 1
    ext i
    fin_cases i <;> simp [binaryFourierThree, mulVec, dotProduct, Fin.sum_univ_succ,
      Pi.single_apply, CharTwo.add_self_eq_zero] <;> linear_combination hc
  have hdw : D.val *ᵥ Fin.cons 0 (Pi.single 0 1) = Fin.cons 0 (Pi.single 0 (v 0)) := by
    rw [hd]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Pi.single_apply]
      split_ifs with hj
      · subst j; simp
      · simp
  rw [hdv, hBv, hdw, ← hExt, extendSpecialHom_matrix, extendMatrix_mulVec] at h
  exact congrArg Fin.tail h
end Atlas.Unitary
