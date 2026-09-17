import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Center

namespace Atlas.Algebra

/-- A central extension with perfect total group cannot have a homomorphic
section unless its kernel is trivial. No finiteness or multiplier is assumed. -/
theorem perfect_central_section_kernel_eq_bot {G Q : Type*} [Group G] [Group Q]
    [Group.IsPerfect G] (f : G →* Q) (hc : f.ker ≤ Subgroup.center G)
    (s : Q →* G) (hs : f.comp s=MonoidHom.id Q) : f.ker=⊥ := by
  have hfs (q : Q) : f (s q)=q := DFunLike.congr_fun hs q
  let r (g : G) := g * (s (f g))⁻¹
  have hr (g : G) : r g ∈ f.ker := by
    change f (g * (s (f g))⁻¹)=1
    rw [map_mul,map_inv,hfs,mul_inv_cancel]
  have hcancel (g : G) : r g * s (f g)=g := by simp [r,mul_assoc]
  let R : G →* Subgroup.center G := {
    toFun := fun g => ⟨r g,hc (hr g)⟩
    map_one' := by apply Subtype.ext; simp [r]
    map_mul' := by
      intro g h
      apply Subtype.ext
      change r (g*h)=r g*r h
      apply mul_right_cancel (b := s (f (g*h)))
      rw [hcancel,map_mul,map_mul]
      have hh := Subgroup.mem_center_iff.mp (hc (hr h)) (s (f g))
      calc
        g*h = (r g*s (f g))*(r h*s (f h)) := by rw [hcancel,hcancel]
        _ = (r g*(s (f g)*r h))*s (f h) := by simp only [mul_assoc]
        _ = (r g*(r h*s (f g)))*s (f h) := by rw [hh]
        _ = (r g*r h)*(s (f g)*s (f h)) := by simp only [mul_assoc] }
  letI : Group.IsPerfect R.range := Group.IsPerfect.ofSurjective R.rangeRestrict_surjective
  have hR (g : G) : R g=1 := congrArg Subtype.val (Subsingleton.elim (R.rangeRestrict g) 1)
  apply le_antisymm ?_ bot_le
  intro g hg
  change g=1
  have h := congrArg Subtype.val (hR g)
  change r g=1 at h
  have hfg : f g=1 := hg
  simpa [r,hfg] using h

end Atlas.Algebra
