import Atlas.LinearGroups.Orthogonal.ElementaryTransitivity
import Atlas.LinearGroups.Orthogonal.SpecialStandard

/-! # The concrete two-pair frames and elementary shell transitivity for standard B/D -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F : Type*} [Field F]

def wittTwoFrameD (n : ℕ) : WittTwoFrame (formD (n+2) F) where
  e₁ := e 0
  f₁ := f 0
  e₂ := e 1
  f₂ := f 1
  qe₁ := formD_e _
  qf₁ := formD_f _
  qe₂ := formD_e _
  qf₂ := formD_f _
  pair₁ := polarD_ef _
  pair₂ := polarD_ef _
  ee := by rw [polarD_e]; simp [e, Pi.single_apply]
  ef := by rw [polarD_f]; simp [e, Pi.single_apply]
  fe := by rw [polarD_e]; simp [f, Pi.single_apply]
  ff := by rw [polarD_f]; simp [f, Pi.single_apply]

def wittTwoFrameB (n : ℕ) : WittTwoFrame (formB (n+2) F) where
  e₁ := ((wittTwoFrameD n).e₁, 0)
  f₁ := ((wittTwoFrameD n).f₁, 0)
  e₂ := ((wittTwoFrameD n).e₂, 0)
  f₂ := ((wittTwoFrameD n).f₂, 0)
  qe₁ := by simp only [formB_apply, (wittTwoFrameD n).qe₁, zero_pow (by decide : 2 ≠ 0), add_zero]
  qf₁ := by simp only [formB_apply, (wittTwoFrameD n).qf₁, zero_pow (by decide : 2 ≠ 0), add_zero]
  qe₂ := by simp only [formB_apply, (wittTwoFrameD n).qe₂, zero_pow (by decide : 2 ≠ 0), add_zero]
  qf₂ := by simp only [formB_apply, (wittTwoFrameD n).qf₂, zero_pow (by decide : 2 ≠ 0), add_zero]
  pair₁ := by simp only [polarB_apply, (wittTwoFrameD n).pair₁, mul_zero, add_zero]
  pair₂ := by simp only [polarB_apply, (wittTwoFrameD n).pair₂, mul_zero, add_zero]
  ee := by simp only [polarB_apply, (wittTwoFrameD n).ee, mul_zero, add_zero]
  ef := by simp only [polarB_apply, (wittTwoFrameD n).ef, mul_zero, add_zero]
  fe := by simp only [polarB_apply, (wittTwoFrameD n).fe, mul_zero, add_zero]
  ff := by simp only [polarB_apply, (wittTwoFrameD n).ff, mul_zero, add_zero]

theorem elementary_transportB (n : ℕ) (h2 : (2 : F) ≠ 0)
    (u v : VectorB (n+2) F) (hu : formB (n+2) F u ≠ 0)
    (hval : formB (n+2) F u = formB (n+2) F v) :
    ∃ g : O_B (n+2) F, g ∈ elementarySubgroup (formB (n+2) F) ∧ g.val u = v :=
  elementary_transport_equal_value (formB (n+2) F) (wittTwoFrameB n)
    (polarB_nondegenerate h2) h2 u v hu hval

theorem elementary_transportD (n : ℕ) (h2 : (2 : F) ≠ 0)
    (u v : VectorD (n+2) F) (hu : formD (n+2) F u ≠ 0)
    (hval : formD (n+2) F u = formD (n+2) F v) :
    ∃ g : O_DPlus (n+2) F, g ∈ elementarySubgroup (formD (n+2) F) ∧ g.val u = v :=
  elementary_transport_equal_value (formD (n+2) F) (wittTwoFrameD n)
    polarD_nondegenerate h2 u v hu hval

end Atlas.Orthogonal
