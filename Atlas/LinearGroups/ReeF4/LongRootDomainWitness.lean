import Atlas.LinearAlgebra.SemilinearHyperplane
import Atlas.LinearGroups.ReeF4.LongRootInvolution
import Atlas.LinearGroups.ReeF4.DomainDiagonalFunctional

/-! An explicit long-root transport from the diagonal-coordinate kernel to its complement.
This is a local statement, not yet full star preservation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

private abbrev B := ZMod 2

def extensionInput : ⋀[B]^2 (TraceZero B) :=
  wedge (rootVector (0,1)) (rootVector (2,6)) + wedge (diagonalVector 0) (rootVector (1,4))

def extensionImage : ⋀[B]^2 (TraceZero B) :=
  wedge (longRootImage (.inr (0,1))) (longRootImage (.inr (2,6))) +
    wedge (longRootImage (.inl 0)) (longRootImage (.inr (1,4)))

theorem extensionInput_mem : extensionInput ∈ StarCarrier (F := B) := by
  constructor
  · change exteriorPolar extensionInput = 0
    simp only [extensionInput, _root_.map_add, exteriorPolar_wedge]
    decide
  · change exteriorCross extensionInput = 0
    simp only [extensionInput, _root_.map_add, exteriorCross_wedge]
    decide

theorem extensionImage_mem : extensionImage ∈ StarCarrier (F := B) := by
  constructor
  · change exteriorPolar extensionImage = 0
    simp only [extensionImage, _root_.map_add, exteriorPolar_wedge]
    decide
  · change exteriorCross extensionImage = 0
    simp only [extensionImage, _root_.map_add, exteriorCross_wedge]
    decide

theorem extensionInput_diagonal : exteriorDiagonal extensionInput = 0 := by
  simp [extensionInput, rootVector]

theorem extensionImage_diagonal : exteriorDiagonal extensionImage = 1 := by
  simp only [extensionImage, _root_.map_add, exteriorDiagonal_wedge]
  decide

theorem extensionImage_transport :
    exteriorPower.map 2 (longRootLinear (F := B)) extensionInput = extensionImage := by
  have hw (u v : TraceZero B) :
      exteriorPower.map 2 (longRootLinear (F := B)) (wedge u v) =
        wedge (longRootLinear u) (longRootLinear v) := by
    simp only [wedge, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  simp only [extensionInput, _root_.map_add, hw, longRootLinear_root,
    longRootLinear_diagonal_zero, extensionImage]
  rfl

/-- Compatibility with t removes the remaining one-coordinate ambiguity once
all values on the diagonal kernel have been fixed. -/
theorem extension_unique_of_longRoot
    (f g : StarCarrier (F := B) →ₗ[B] TraceZero B)
    (hk : ∀ x : StarCarrier (F := B), exteriorDiagonal x.val = 0 → f x = g x)
    (hf : f ⟨extensionImage, extensionImage_mem⟩ =
      longRootLinear (f ⟨extensionInput, extensionInput_mem⟩))
    (hg : g ⟨extensionImage, extensionImage_mem⟩ =
      longRootLinear (g ⟨extensionInput, extensionInput_mem⟩)) : f = g := by
  apply Atlas.semilinear_ext_on_kernel_and_unit (RingHom.id B)
    (exteriorDiagonal.comp (StarCarrier (F := B)).subtype) f g
    ⟨extensionImage, extensionImage_mem⟩ extensionImage_diagonal hk
  rw [hf, hg, hk ⟨extensionInput, extensionInput_mem⟩ extensionInput_diagonal]

end Atlas.ReeF4

