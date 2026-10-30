import Atlas.LinearGroups.ReeF4.ChartPositiveConjugates
import Atlas.LinearGroups.ReeF4.SpecialNegativeA2Chart

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem chartTerminalWord_inverse_root {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (a : F) :
    ((negativeA2ChartWord hcard a)⁻¹).val (rootVector (F := F) (0,0))=
      (nextChartPoint hcard a).val := by
  have hs : (weylSigma (F := F))⁻¹=weylSigma := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using weylSigma_square (F := F)
  have hl : (longSL2Equiv a (theta F m a))⁻¹=longSL2Equiv a (theta F m a) := by
    apply LinearEquiv.ext
    intro w
    rfl
  have hs0 : weylSigma (rootVector (F := F) (0,0))=rootVector (2,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (0,0)))
  change ((((weylSigma (F := F)) * longSL2Equiv a (theta F m a))⁻¹)
    (rootVector (F := F) (0,0)))=_
  rw [mul_inv_rev,hl,hs]
  change longSL2Equiv a (theta F m a) (weylSigma (rootVector (F := F) (0,0)))=_
  rw [hs0]
  apply Subtype.ext
  change longSL2Formula a (theta F m a) (rootVector (F := F) (2,0)).val=_
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [longSL2Formula,nextChartPoint,rootVector,Pi.single_apply,smul_eq_mul]
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [longSL2Formula,nextChartPoint,rootVector,Pi.single_apply,smul_eq_mul]

theorem chartFinalWeyl_root (m : ℕ) :
    (chartShortPrefix (F := F) m 3).val (rootVector (0,0))=rootVector (0,7) := by
  have h0 : weylSigma (rootVector (F := F) (0,0))=rootVector (2,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (0,0)))
  have h1 : weylRho (rootVector (F := F) (2,0))=rootVector (2,1) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 0 (.inr (2,0)))
  have h2 : weylSigma (rootVector (F := F) (2,1))=rootVector (0,2) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (2,1)))
  have h3 : weylRho (rootVector (F := F) (0,2))=rootVector (0,5) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 0 (.inr (0,2)))
  have h4 : weylSigma (rootVector (F := F) (0,5))=rootVector (2,6) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (0,5)))
  have h5 : weylRho (rootVector (F := F) (2,6))=rootVector (2,7) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 0 (.inr (2,6)))
  have h6 : weylSigma (rootVector (F := F) (2,7))=rootVector (0,7) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (2,7)))
  change weylSigma (weylRho (weylSigma (weylRho (weylSigma (weylRho (weylSigma (rootVector (F := F) (0,0))))))))=rootVector (0,7)
  rw [h0,h1,h2,h3,h4,h5,h6]
end Atlas.ReeF4
