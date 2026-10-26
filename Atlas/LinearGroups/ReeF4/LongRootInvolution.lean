import Atlas.LinearGroups.ReeF4.MarkedBasis

/-! Wilson R1 section 4's long-root element t, directly on the marked Albert space.
No preservation of the unfinished star product is assumed here. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def longRootImage : TraceZeroCoordinate → TraceZero F
  | .inl 0 => diagonalVector 0 + rootVector (1,3)
  | .inl _ => diagonalVector 1
  | .inr (0,1) => rootVector (0,1) + rootVector (2,1)
  | .inr (0,2) => rootVector (0,2) + rootVector (2,2) + rootVector (2,1) + rootVector (0,1)
  | .inr (0,3) => rootVector (0,3) + rootVector (2,4)
  | .inr (0,6) => rootVector (0,6) + rootVector (0,5)
  | .inr (0,7) => rootVector (0,7) + rootVector (2,7)
  | .inr (1,2) => rootVector (1,2) + rootVector (1,1)
  | .inr (1,4) => rootVector (1,4) + diagonalVector 1 + rootVector (1,3)
  | .inr (1,6) => rootVector (1,6) + rootVector (1,5)
  | .inr (2,0) => rootVector (2,0) + rootVector (0,0)
  | .inr (2,2) => rootVector (2,2) + rootVector (2,1)
  | .inr (2,3) => rootVector (2,3) + rootVector (0,4)
  | .inr (2,5) => rootVector (2,5) + rootVector (0,5)
  | .inr (2,6) => rootVector (2,6) + rootVector (0,6) + rootVector (2,5) + rootVector (0,5)
  | .inr r => rootVector r

def longRootLinear : TraceZero F →ₗ[F] TraceZero F := markedBasis.constr F longRootImage

@[simp] theorem longRootLinear_basis (i : TraceZeroCoordinate) :
    longRootLinear (markedBasis (F := F) i) = longRootImage i := by
  simp [longRootLinear]

@[simp] theorem longRootLinear_root (r : ShortRootLabel) :
    longRootLinear (rootVector (F := F) r) = longRootImage (.inr r) := by
  rw [← markedBasis_root]
  exact longRootLinear_basis _

@[simp] theorem longRootLinear_diagonal_zero :
    longRootLinear (diagonalVector (F := F) 0) = diagonalVector 0 + rootVector (1,3) := by
  simpa [markedBasis_diagonal, longRootImage] using longRootLinear_basis (F := F) (.inl 0)

@[simp] theorem longRootLinear_diagonal_one :
    longRootLinear (diagonalVector (F := F) 1) = diagonalVector 1 := by
  simpa [markedBasis_diagonal, longRootImage] using longRootLinear_basis (F := F) (.inl 1)

private theorem double_zero (x : TraceZero F) : x + x = 0 := by
  rw [← two_smul F, CharTwo.two_eq_zero, zero_smul]

private theorem two_nsmul_zero (x : TraceZero F) : (2 : ℕ) • x = 0 := by
  simpa only [two_smul] using double_zero x

private theorem four_nsmul_zero (x : TraceZero F) : (4 : ℕ) • x = 0 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_smul, two_nsmul_zero]

private theorem two_zsmul_zero (x : TraceZero F) : (2 : ℤ) • x = 0 := by
  simpa only [ofNat_zsmul] using two_nsmul_zero x

private theorem four_zsmul_zero (x : TraceZero F) : (4 : ℤ) • x = 0 := by
  simpa only [ofNat_zsmul] using four_nsmul_zero x

set_option maxHeartbeats 800000 in
-- Verify the 26 marked basis images; this is independent of field cardinality.
theorem longRootLinear_square : (longRootLinear (F := F)).comp longRootLinear = LinearMap.id := by
  apply markedBasis.ext
  intro i
  rcases i with i | ⟨b,j⟩
  · fin_cases i <;>
      simp [LinearMap.comp_apply, markedBasis_diagonal, longRootImage, double_zero,
        add_assoc, ← add_rotate] <;> abel_nf <;>
        first | rfl | simp [two_nsmul_zero, four_nsmul_zero, two_zsmul_zero, four_zsmul_zero]
  · fin_cases b <;> fin_cases j <;>
      simp [LinearMap.comp_apply, markedBasis_root, longRootImage, double_zero,
        add_assoc, ← add_rotate] <;> abel_nf <;>
        first | rfl | simp [two_nsmul_zero, four_nsmul_zero, two_zsmul_zero, four_zsmul_zero]

def longRootEquiv : TraceZero F ≃ₗ[F] TraceZero F :=
  LinearEquiv.ofInvolutive (longRootLinear (F := F))
    (fun x => LinearMap.congr_fun (longRootLinear_square (F := F)) x)

end Atlas.ReeF4
