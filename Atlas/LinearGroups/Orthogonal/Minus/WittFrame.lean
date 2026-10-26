import Atlas.LinearGroups.Orthogonal.Minus.Basic
import Atlas.LinearGroups.Orthogonal.ElementaryTransitivityAllChar

/-! Concrete two-pair frames and elementary transport with the norm-plane tail. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.Quadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def wittTwoFrame (hdeg : Module.finrank F K = 2) (n : ℕ) :
    WittTwoFrame (form hdeg (n+2)) where
  e₁ := ((wittTwoFrameD n).e₁, 0)
  f₁ := ((wittTwoFrameD n).f₁, 0)
  e₂ := ((wittTwoFrameD n).e₂, 0)
  f₂ := ((wittTwoFrameD n).f₂, 0)
  qe₁ := by simp only [form_apply, (wittTwoFrameD n).qe₁, ← normForm_apply hdeg, map_zero, add_zero]
  qf₁ := by simp only [form_apply, (wittTwoFrameD n).qf₁, ← normForm_apply hdeg, map_zero, add_zero]
  qe₂ := by simp only [form_apply, (wittTwoFrameD n).qe₂, ← normForm_apply hdeg, map_zero, add_zero]
  qf₂ := by simp only [form_apply, (wittTwoFrameD n).qf₂, ← normForm_apply hdeg, map_zero, add_zero]
  pair₁ := by simp only [polar_apply, (wittTwoFrameD n).pair₁, map_zero, add_zero]
  pair₂ := by simp only [polar_apply, (wittTwoFrameD n).pair₂, map_zero, add_zero]
  ee := by simp only [polar_apply, (wittTwoFrameD n).ee, map_zero, add_zero]
  ef := by simp only [polar_apply, (wittTwoFrameD n).ef, map_zero, add_zero]
  fe := by simp only [polar_apply, (wittTwoFrameD n).fe, map_zero, add_zero]
  ff := by simp only [polar_apply, (wittTwoFrameD n).ff, map_zero, add_zero]

theorem elementary_singular_transport (hdeg : Module.finrank F K = 2) (n : ℕ)
    (u v : Vector (n+2) F K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : form hdeg (n+2) u = 0) (hqv : form hdeg (n+2) v = 0) :
    ∃ g : O hdeg (n+2), g ∈ E hdeg (n+2) ∧ g.val u = v :=
  elementary_singular_transport_all_char _ (wittTwoFrame hdeg n)
    (polar_nondegenerate hdeg _) u v hu hv hqu hqv

theorem elementary_pair_transport (hdeg : Module.finrank F K = 2) (n : ℕ)
    (e f u v : Vector (n+2) F K)
    (he : form hdeg (n+2) e = 0) (hf : form hdeg (n+2) f = 0)
    (hu : form hdeg (n+2) u = 0) (hv : form hdeg (n+2) v = 0)
    (hef : (form hdeg (n+2)).polarBilin e f = 1)
    (huv : (form hdeg (n+2)).polarBilin u v = 1) :
    ∃ g : O hdeg (n+2), g ∈ E hdeg (n+2) ∧ g.val e = u ∧ g.val f = v :=
  elementary_pair_transport_all_char _ (wittTwoFrame hdeg n)
    (polar_nondegenerate hdeg _) e f u v he hf hu hv hef huv
end Atlas.Orthogonal.Minus
