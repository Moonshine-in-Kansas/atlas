import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Units.Basic
/-! unit scaling and a root-faithful projection.
Independent of Chevalley constructions; parameter multiplication need not commute. -/
namespace Atlas.GroupTheory
variable {R G H : Type*} [Monoid R] [Group G] [Group H]

/-- Elements that scale one parametrized root subgroup by a unit. -/
def rootScalingSubgroup (x : R → G) : Subgroup G where
  carrier := {g | ∃ a : Rˣ, ∀ t, g*x t = x (a.val*t)*g}
  one_mem' := ⟨1, by intro t; simp⟩
  mul_mem' := by
    rintro g h ⟨a,ha⟩ ⟨b,hb⟩
    refine ⟨a*b, ?_⟩
    intro t
    calc
      (g*h)*x t = g*(h*x t) := mul_assoc _ _ _
      _ = g*(x (b.val*t)*h) := by rw [hb]
      _ = (g*x (b.val*t))*h := (mul_assoc _ _ _).symm
      _ = (x (a.val*(b.val*t))*g)*h := by rw [ha]
      _ = x ((a*b).val*t)*(g*h) := by simp only [Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro g ⟨a,ha⟩
    refine ⟨a⁻¹, ?_⟩
    intro t
    have h := ha ((a⁻¹).val*t)
    have hc : a.val*((a⁻¹).val*t)=t := by simp [← mul_assoc]
    rw [hc] at h
    have hh := congrArg (fun z : G => g⁻¹*z*g⁻¹) h
    simpa [mul_assoc] using hh.symm

/-- Projection faithfulness on the root parameter forces a kernel scaling
factor to be one. Only injectivity of this root map is used. -/
theorem rootScaling_kernel_commute (x : R → G) (φ : G →* H)
    (hinj : Function.Injective (fun t => φ (x t))) {g : G}
    (hg : g ∈ rootScalingSubgroup x) (hker : φ g=1) (t : R) : Commute g (x t) := by
  obtain ⟨a,ha⟩ := hg
  have hh := congrArg φ (ha 1)
  simp only [map_mul,hker,one_mul,mul_one] at hh
  have he : (1:R)=a.val := hinj hh
  exact (ha t).trans (by rw [← he,one_mul])
end Atlas.GroupTheory
