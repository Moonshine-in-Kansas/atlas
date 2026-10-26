import Atlas.LinearGroups.F4.Simplicity
import Mathlib.GroupTheory.Subgroup.Center

/-! The actual full Albert group has trivial center; no projective quotient
is needed, including over the binary field. -/
namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

theorem center_eq_bot : Subgroup.center (Model F)=⊥ := by
  letI := isSimple (F:=F)
  rcases (inferInstance : (Subgroup.center (Model F)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨a,b,hab⟩ := exists_mul_ne_mul (F:=F)
    have hb : b∈Subgroup.center (Model F) := by rw [h]; trivial
    exact (hab ((Subgroup.mem_center_iff.mp hb) a)).elim

end Atlas.F4
