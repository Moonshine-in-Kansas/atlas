import Atlas.LinearGroups.Unitary.ThreeRootGeneration
import Atlas.LinearGroups.Unitary.GeneratedNormal

/-! The matrix image of the actual transvection-generated subgroup in the proved
hyperbolic basis. This keeps all subsequent matrix words tied to the public SU₃. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Actual conjugation of the retained SU₃ carrier into hyperbolic coordinates. -/
def threeWittHom (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) :
    SU F K 3 hdeg →* Matrix (Fin 3) (Fin 3) K where
  toFun g := (wittThreeMatrix a b)⁻¹ * g.val * wittThreeMatrix a b
  map_one' := by
    change (wittThreeMatrix a b)⁻¹ * 1 * wittThreeMatrix a b = 1
    rw [mul_one, nonsing_inv_mul _ (wittThreeMatrix_det_unit a b ha)]
  map_mul' g h := by
    change (wittThreeMatrix a b)⁻¹ * (g.val*h.val) * wittThreeMatrix a b = _
    simp only [mul_assoc, ← mul_assoc (wittThreeMatrix a b) (wittThreeMatrix a b)⁻¹,
      mul_nonsing_inv _ (wittThreeMatrix_det_unit a b ha), one_mul]

theorem threeWittHom_root (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (c d : K) (hcd : rootThreeCondition (F := F) c d) :
    threeWittHom hdeg a b ha (rootThreeUnitary hdeg a b ha hb c d hcd) =
      rootThreeMatrix (F := F) c d := by
  change (wittThreeMatrix a b)⁻¹ * (wittThreeMatrix a b *
    rootThreeMatrix (F := F) c d * (wittThreeMatrix a b)⁻¹) * wittThreeMatrix a b = _
  simp only [mul_assoc, ← mul_assoc (wittThreeMatrix a b)⁻¹ (wittThreeMatrix a b),
    nonsing_inv_mul _ (wittThreeMatrix_det_unit a b ha), one_mul, mul_one]

/-- This is an image of the actual generated subgroup, not a replacement definition of SU₃. -/
def threeGeneratedMatrices (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) : Submonoid (Matrix (Fin 3) (Fin 3) K) :=
  (transvectionGenerated hdeg (n := 3)).toSubmonoid.map (threeWittHom hdeg a b ha)

private theorem rootThree_center_apply (z : K) (x : Fin 3 → K) :
    rootThreeMatrix (F := F) 0 z *ᵥ x = x + (z*x 2) • Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [rootThreeMatrix, mulVec, dotProduct, Fin.sum_univ_succ, add_comm]

/-- The actual standard transvection on the first hyperbolic line maps to the
central root matrix, so these roots belong to the actual generated subgroup image. -/
theorem rootThree_center_mem_generatedMatrices (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (z : K) (hz : z + conjugation F K z = 0) :
    rootThreeMatrix (F := F) 0 z ∈ threeGeneratedMatrices hdeg a b ha := by
  let P := wittThreeMatrix a b
  let v : Fin 3 → K := P *ᵥ Pi.single 0 1
  have hv : hermitian F K v v = 0 := by
    rw [wittThreeMatrix_preserves a b ha hb]
    simp [hyperbolicThreeForm]
  let T := transvection hdeg v z hv hz
  have hT : T ∈ transvectionGenerated hdeg := transvection_mem_generated hdeg v hv z hz
  refine ⟨T, hT, ?_⟩
  have hTP : T.val * P = P * rootThreeMatrix (F := F) 0 z := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← mulVec_mulVec, ← mulVec_mulVec, rootThree_center_apply]
    change transvectionMatrix (F := F) v z *ᵥ (P *ᵥ Pi.single i 1) = _
    rw [transvectionMatrix_apply]
    have hp : hermitian F K (P *ᵥ Pi.single i 1) v = (Pi.single i 1 : Fin 3 → K) 2 := by
      change hermitian F K (P *ᵥ Pi.single i 1) (P *ᵥ Pi.single 0 1) = _
      rw [wittThreeMatrix_preserves a b ha hb]
      simp [hyperbolicThreeForm]
    rw [hp, mulVec_add, mulVec_smul]
  change P⁻¹ * T.val * P = rootThreeMatrix (F := F) 0 z
  rw [mul_assoc, hTP, ← mul_assoc, nonsing_inv_mul _ (wittThreeMatrix_det_unit a b ha), one_mul]


/-- The opposite long-root matrix, again before the actual coordinate transfer. -/
def lowerRootThreeMatrix (z : K) : Matrix (Fin 3) (Fin 3) K := !![1,0,0; 0,1,0; z,0,1]

omit [Finite K] in
private theorem lowerRootThree_apply (z : K) (x : Fin 3 → K) :
    lowerRootThreeMatrix z *ᵥ x = x + (z*x 0) • Pi.single 2 1 := by
  ext i
  fin_cases i <;> simp [lowerRootThreeMatrix, mulVec, dotProduct,
    Fin.sum_univ_succ, add_comm]

theorem lowerRootThree_mem_generatedMatrices (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (z : K) (hz : z + conjugation F K z = 0) :
    lowerRootThreeMatrix z ∈ threeGeneratedMatrices hdeg a b ha := by
  let P := wittThreeMatrix a b
  let v : Fin 3 → K := P *ᵥ Pi.single 2 1
  have hv : hermitian F K v v = 0 := by
    rw [wittThreeMatrix_preserves a b ha hb]
    simp [hyperbolicThreeForm]
  let T := transvection hdeg v z hv hz
  have hT : T ∈ transvectionGenerated hdeg := transvection_mem_generated hdeg v hv z hz
  refine ⟨T, hT, ?_⟩
  have hTP : T.val * P = P * lowerRootThreeMatrix z := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← mulVec_mulVec, ← mulVec_mulVec, lowerRootThree_apply]
    change transvectionMatrix (F := F) v z *ᵥ (P *ᵥ Pi.single i 1) = _
    rw [transvectionMatrix_apply]
    have hp : hermitian F K (P *ᵥ Pi.single i 1) v = (Pi.single i 1 : Fin 3 → K) 0 := by
      change hermitian F K (P *ᵥ Pi.single i 1) (P *ᵥ Pi.single 2 1) = _
      rw [wittThreeMatrix_preserves a b ha hb]
      simp [hyperbolicThreeForm]
    rw [hp, mulVec_add, mulVec_smul]
  change P⁻¹ * T.val * P = lowerRootThreeMatrix z
  rw [mul_assoc, hTP, ← mul_assoc, nonsing_inv_mul _ (wittThreeMatrix_det_unit a b ha), one_mul]

/-- The Weyl matrix is a word in three actual long-root transvections. -/
theorem longWeylThree_word (z : K) (hz : z ≠ 0) :
    rootThreeMatrix (F := F) 0 z * lowerRootThreeMatrix (-z⁻¹) *
      rootThreeMatrix (F := F) 0 z = longWeylThreeMatrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootThreeMatrix, lowerRootThreeMatrix, longWeylThreeMatrix,
      mul_apply, Fin.sum_univ_succ, hz]

theorem longWeyl_mem_generatedMatrices (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (z : K) (hz : z ≠ 0) (htrace : z + conjugation F K z = 0) :
    longWeylThreeMatrix z ∈ threeGeneratedMatrices hdeg a b ha := by
  have hzi : -z⁻¹ + conjugation F K (-z⁻¹) = 0 := by
    have hs : conjugation F K z = -z := by linear_combination htrace
    simp [map_neg, map_inv₀, hs]
  rw [← longWeylThree_word (F := F) z hz]
  exact (threeGeneratedMatrices hdeg a b ha).mul_mem
    ((threeGeneratedMatrices hdeg a b ha).mul_mem
      (rootThree_center_mem_generatedMatrices hdeg a b ha hb z htrace)
      (lowerRootThree_mem_generatedMatrices hdeg a b ha hb _ hzi))
    (rootThree_center_mem_generatedMatrices hdeg a b ha hb z htrace)

theorem torusThree_mem_generatedMatrices (hdeg : Module.finrank F K = 2) (a b : K)
    (ha : a * conjugation F K a = -1) (hb : b + conjugation F K b = 1)
    (t : K) (ht : t ≠ 0) (hfix : conjugation F K t = t) :
    torusThreeMatrix t ∈ threeGeneratedMatrices hdeg a b ha := by
  obtain ⟨z, hz, htrace⟩ := exists_nonzero_trace_zero hdeg
  have hs : conjugation F K z = -z := by linear_combination htrace
  have hzt : -z/t ≠ 0 := div_ne_zero (neg_ne_zero.mpr hz) ht
  have htrace' : (-z/t) + conjugation F K (-z/t) = 0 := by
    simp [map_div₀, map_neg, hfix, hs, neg_div]
  have he : longWeylThreeMatrix z * longWeylThreeMatrix (-z/t) = torusThreeMatrix t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [longWeylThreeMatrix, torusThreeMatrix, mul_apply, Fin.sum_univ_succ] <;> field_simp
  rw [← he]
  exact (threeGeneratedMatrices hdeg a b ha).mul_mem
    (longWeyl_mem_generatedMatrices hdeg a b ha hb z hz htrace)
    (longWeyl_mem_generatedMatrices hdeg a b ha hb _ hzt htrace')
end Atlas.Unitary
