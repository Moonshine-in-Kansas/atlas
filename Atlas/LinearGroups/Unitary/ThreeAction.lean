import Atlas.LinearGroups.Unitary.ThreeMatrixModel
import Atlas.LinearGroups.Unitary.ThreePointParameters
import Atlas.LinearGroups.Unitary.IsotropicTransport
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! # The actual doubly transitive isotropic action in dimension three -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
open scoped LinearAlgebra.Projectivization
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem wittThree_mulVec_ne_zero (a b : K) (ha : a * conjugation F K a = -1)
    (x : Fin 3 → K) (hx : x ≠ 0) : wittThreeMatrix a b *ᵥ x ≠ 0 := by
  intro he
  have h := congrArg (fun v => (wittThreeMatrix a b)⁻¹ *ᵥ v) he
  rw [mulVec_mulVec, nonsing_inv_mul _ (wittThreeMatrix_det_unit a b ha), one_mulVec,
    mulVec_zero] at h
  exact hx h

def threePoint (a b : K) (ha : a * conjugation F K a = -1)
    (hb : b + conjugation F K b = 1) (x : Fin 3 → K) (hx : x ≠ 0)
    (hiso : hyperbolicThreeForm (F := F) x x = 0) : IsotropicPoints F K 3 :=
  isotropicPoint (wittThreeMatrix a b *ᵥ x) (wittThree_mulVec_ne_zero a b ha x hx)
    ((wittThreeMatrix_preserves a b ha hb x x).trans hiso)

def threeFirstPoint (a b : K) (ha : a * conjugation F K a = -1)
    (hb : b + conjugation F K b = 1) : IsotropicPoints F K 3 :=
  threePoint a b ha hb (Pi.single 0 1) (by simp) (by simp [hyperbolicThreeForm, Pi.single_apply])

def threeLastPoint (a b : K) (ha : a * conjugation F K a = -1)
    (hb : b + conjugation F K b = 1) : IsotropicPoints F K 3 :=
  threePoint a b ha hb (Pi.single 2 1) (by simp) (by simp [hyperbolicThreeForm, Pi.single_apply])

theorem rootThreeUnitary_apply_witt (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (c d : K) (hcd : rootThreeCondition (F := F) c d) (x : Fin 3 → K) :
    (rootThreeUnitary hdeg a b ha hb c d hcd).val *ᵥ (wittThreeMatrix a b *ᵥ x) =
      wittThreeMatrix a b *ᵥ (rootThreeMatrix (F := F) c d *ᵥ x) := by
  change (wittThreeMatrix a b * rootThreeMatrix (F := F) c d *
    (wittThreeMatrix a b)⁻¹) *ᵥ (wittThreeMatrix a b *ᵥ x) = _
  simp only [mulVec_mulVec, mul_assoc, nonsing_inv_mul _ (wittThreeMatrix_det_unit a b ha),
    mul_one]

theorem rootThreeUnitary_fixes_first (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (c d : K) (hcd : rootThreeCondition (F := F) c d) :
    rootThreeUnitary hdeg a b ha hb c d hcd • threeFirstPoint a b ha hb =
      threeFirstPoint a b ha hb := by
  apply Subtype.ext
  change _ • Projectivization.mk K _ _ = Projectivization.mk K _ _
  rw [Projectivization.smul_mk]
  congr 1
  change (rootThreeUnitary hdeg a b ha hb c d hcd).val *ᵥ
    (wittThreeMatrix a b *ᵥ Pi.single 0 1) = _
  rw [rootThreeUnitary_apply_witt]
  congr 1
  ext i
  fin_cases i <;> simp [rootThreeMatrix, mulVec_single_one, Pi.single_apply]

/-- The actual root group covers every isotropic point other than its fixed point. -/
theorem three_root_transporter (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (p : IsotropicPoints F K 3) (hp : p ≠ threeFirstPoint a b ha hb) :
    ∃ g : SU F K 3 hdeg, g • threeFirstPoint a b ha hb = threeFirstPoint a b ha hb ∧
      g • threeLastPoint a b ha hb = p := by
  let P := wittThreeMatrix a b
  let x := P⁻¹ *ᵥ p.val.rep
  have hPx : P *ᵥ x = p.val.rep := by
    rw [mulVec_mulVec, mul_nonsing_inv P (wittThreeMatrix_det_unit a b ha), one_mulVec]
  have hiso : hyperbolicThreeForm (F := F) x x = 0 := by
    rw [← wittThreeMatrix_preserves a b ha hb, hPx]
    exact isotropic_rep p
  have hlast : x 2 ≠ 0 := by
    intro he
    have hx := three_isotropic_last_zero x hiso he
    apply hp
    apply Subtype.ext
    change p.val = Projectivization.mk K (P *ᵥ Pi.single 0 1) _
    rw [← Projectivization.mk_rep p.val, Projectivization.mk_eq_mk_iff']
    refine ⟨x 0, ?_⟩
    rw [← hPx, hx, mulVec_smul]
    simp
  obtain ⟨hcond, hx⟩ := three_isotropic_parameters hdeg x hiso hlast
  let g := rootThreeUnitary hdeg a b ha hb (x 1 / x 2) (x 0 / x 2) hcond
  refine ⟨g, rootThreeUnitary_fixes_first hdeg a b ha hb _ _ hcond, ?_⟩
  have hv : x 2 • (g.val *ᵥ (P *ᵥ Pi.single 2 1)) = p.val.rep := by
    rw [rootThreeUnitary_apply_witt]
    rw [← mulVec_smul, ← hx, hPx]
  apply Subtype.ext
  change g • Projectivization.mk K (P *ᵥ Pi.single 2 1) _ = p.val
  rw [Projectivization.smul_mk]
  symm
  rw [← Projectivization.mk_rep p.val, Projectivization.mk_eq_mk_iff']
  exact ⟨x 2, hv⟩

/-- The full point stabilizer is transitive on every other isotropic point. -/
theorem three_first_stabilizer_pretransitive (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1) :
    MulAction.IsPretransitive
      (MulAction.stabilizer (SU F K 3 hdeg) (threeFirstPoint a b ha hb))
      (SubMulAction.ofStabilizer (SU F K 3 hdeg) (threeFirstPoint a b ha hb)) := by
  constructor
  intro p q
  obtain ⟨g, hgf, hgp⟩ := three_root_transporter hdeg a b ha hb p.val p.prop
  obtain ⟨k, hkf, hkq⟩ := three_root_transporter hdeg a b ha hb q.val q.prop
  have hs : k * g⁻¹ ∈ MulAction.stabilizer (SU F K 3 hdeg) (threeFirstPoint a b ha hb) := by
    change (k * g⁻¹) • threeFirstPoint a b ha hb = threeFirstPoint a b ha hb
    rw [mul_smul, ← hgf, inv_smul_smul, hkf]
    exact hgf.symm
  refine ⟨⟨k * g⁻¹, hs⟩, ?_⟩
  apply Subtype.ext
  change (k * g⁻¹) • p.val = q.val
  rw [← hgp, mul_smul, inv_smul_smul, hkq]

theorem special_three_two_pretransitive (hdeg : Module.finrank F K = 2) :
    MulAction.IsMultiplyPretransitive (SU F K 3 hdeg) (IsotropicPoints F K 3) 2 := by
  obtain ⟨a, b, ha, hb⟩ := exists_witt_parameters hdeg
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive
    (G := SU F K 3 hdeg) (a := threeFirstPoint a b ha hb)).mpr
  rw [MulAction.is_one_pretransitive_iff]
  exact three_first_stabilizer_pretransitive hdeg a b ha hb

theorem special_three_preprimitive (hdeg : Module.finrank F K = 2) :
    MulAction.IsPreprimitive (SU F K 3 hdeg) (IsotropicPoints F K 3) :=
  MulAction.isPreprimitive_of_is_two_pretransitive (special_three_two_pretransitive hdeg)

theorem projective_three_two_pretransitive (hdeg : Module.finrank F K = 2) :
    letI := isotropicAction hdeg (n := 3) (by decide)
    MulAction.IsMultiplyPretransitive (PSU F K 3 hdeg) (IsotropicPoints F K 3) 2 := by
  letI := isotropicAction hdeg (n := 3) (by decide)
  apply MulAction.is_two_pretransitive_iff.mpr
  intro p q r s hpq hrs
  obtain ⟨g, hg, hh⟩ := MulAction.is_two_pretransitive_iff.mp
    (special_three_two_pretransitive hdeg) hpq hrs
  exact ⟨projection F K 3 hdeg g, hg, hh⟩

theorem projective_three_preprimitive (hdeg : Module.finrank F K = 2) :
    letI := isotropicAction hdeg (n := 3) (by decide)
    MulAction.IsPreprimitive (PSU F K 3 hdeg) (IsotropicPoints F K 3) := by
  letI := isotropicAction hdeg (n := 3) (by decide)
  exact MulAction.isPreprimitive_of_is_two_pretransitive (projective_three_two_pretransitive hdeg)

end Atlas.Unitary
