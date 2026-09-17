import Atlas.LinearGroups.Orthogonal.D3ExteriorAction
import Atlas.LinearGroups.Orthogonal.B2ExteriorKernel
import Atlas.LinearGroups.Orthogonal.B2ExteriorScalar

noncomputable section
namespace Atlas.Orthogonal.D3Exterior
open B2Exterior Matrix
variable {F : Type*} [Field F]

theorem scalar_of_exteriorMap_scalar (A : Matrix (Fin 4) (Fin 4) F)
    (c : F) (hc : c ≠ 0) (hA : ∀ w, exteriorMap A w = c • w) :
    ∃ a : F, a ^ 2 = c ∧ A = a • 1 := by
  have hm (i j a b : Fin 4) : A i a * A j b - A j a * A i b =
      c * (((Pi.single a (1 : F)) : Four F) i * ((Pi.single b (1 : F)) : Four F) j -
      ((Pi.single a (1 : F)) : Four F) j * ((Pi.single b (1 : F)) : Four F) i) := by
    have h := hA (wedge (Pi.single a (1 : F)) (Pi.single b (1 : F)))
    rw [exteriorMap_wedge] at h
    have hw : wedge (A *ᵥ Pi.single a 1) (A *ᵥ Pi.single b 1) =
        wedge (c • (Pi.single a 1 : Four F)) (Pi.single b 1) := by
      rw [h]
      ext k
      fin_cases k <;> simp [wedge, Pi.smul_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail] <;> ring
    simpa [Pi.smul_apply, smul_eq_mul, mul_sub, mul_assoc] using wedge_eq_minor hw i j

  have ho (k i : Fin 4) (hki : k ≠ i) : A k i = 0 := by
    obtain ⟨j, hji, hjk⟩ : ∃ j : Fin 4, j ≠ i ∧ j ≠ k := by
      fin_cases k <;> fin_cases i <;> first | contradiction | decide
    have h1 := hm i j i j
    have h2 := hm i k i j
    have h3 := hm j k i j
    simp [hji, hjk, hki, Ne.symm hji, Ne.symm hjk, Ne.symm hki] at h1 h2 h3
    apply mul_left_cancel₀ hc
    linear_combination -A k i * h1 + A j i * h2 - A i i * h3
  have hd (i j : Fin 4) (hij : i ≠ j) : A i i * A j j = c := by
    have h := hm i j i j
    simpa [hij, Ne.symm hij, ho i j hij, ho j i (Ne.symm hij)] using h
  have ha : A 0 0 ≠ 0 := by
    intro h
    have hh := hd 0 1 (by decide)
    exact hc (by simpa [h] using hh.symm)
  have h01 := hd 0 1 (by decide)
  have h02 := hd 0 2 (by decide)
  have h12 := hd 1 2 (by decide)
  have ha2 : A 2 2 ≠ 0 := by
    intro hz
    exact hc (by simpa [hz] using h02.symm)
  have he01 : A 0 0 = A 1 1 := mul_right_cancel₀ ha2 (h02.trans h12.symm)
  have hs : A 0 0 ^ 2 = c := by
    simpa only [← he01, pow_two] using h01
  refine ⟨A 0 0, hs, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    by_cases hi : i = 0
    · subst i; rfl
    apply mul_left_cancel₀ ha
    have hh := hd 0 i (Ne.symm hi)
    linear_combination hh - hs
  · simp [hij, ho i j hij]

/-- Scalar action on the actual split-D coordinates is scalar action on genuine bivectors. -/
theorem toOrthogonal_scalar_iff (g : Matrix.SpecialLinearGroup (Fin 4) F) (c : F) :
    (∀ v, (toOrthogonal g).val v = c • v) ↔
      (∀ w, exteriorMap g.val w = c • w) := by
  constructor
  · intro h w
    apply coordinates.injective
    have hv := h (coordinates w)
    change coordinates (exteriorMap g.val (coordinates.symm (coordinates w))) = c • coordinates w at hv
    simpa only [LinearEquiv.symm_apply_apply, map_smul] using hv
  · intro h v
    change coordinates (exteriorMap g.val (coordinates.symm v)) = c • v
    rw [h, map_smul, LinearEquiv.apply_symm_apply]

/-- The exact full orthogonal kernel consists of square-one scalar matrices. -/
theorem toOrthogonal_eq_one_iff (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    toOrthogonal g = 1 ↔ ∃ a : F, a^2 = 1 ∧ g.val = a • 1 := by
  constructor
  · intro hg
    apply scalar_of_exteriorMap_eq_id
    have hs : ∀ v, (toOrthogonal g).val v = (1 : F) • v := by
      rw [hg]
      intro v
      exact (one_smul F v).symm
    simpa only [one_smul] using (toOrthogonal_scalar_iff g 1).mp hs
  · rintro ⟨a,ha,hg⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change coordinates (exteriorMap g.val (coordinates.symm v)) = v
    rw [hg, exteriorMap_scalar, ha, one_smul, LinearMap.id_apply,
      LinearEquiv.apply_symm_apply]

end Atlas.Orthogonal.D3Exterior
