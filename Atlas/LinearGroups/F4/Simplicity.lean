import Atlas.LinearGroups.F4.PointPrimitivity
import Atlas.LinearGroups.F4.PointFaithfulness
import Atlas.LinearGroups.F4.RadicalNormalClosure
import Atlas.GroupTheory.IwasawaSolvableRadical

/-! All-characteristic simplicity of the full Albert polynomial-and-unit
stabilizer, with no numerical F₄ order in the argument. -/
namespace Atlas.F4
variable {F : Type*} [Field F] [Finite F]

/-- The actual full Albert model is simple over every finite field, including F₂. -/
theorem isSimple : IsSimpleGroup (Model F) := by
  obtain ⟨g,h,hne⟩ := exists_mul_ne_mul (F:=F)
  letI : Nontrivial (Model F) := nontrivial_of_ne (g*h) (h*g) hne
  letI := whiteZeroPoints_primitive (F:=F)
  letI := isPerfect (F:=F)
  letI := radicalSubgroup_solvable (F:=F)
  exact Atlas.GroupTheory.iwasawa_solvable_radical_simple
    (parabolicPoint (F:=F)) radicalSubgroup radicalSubgroup_le_parabolic
    radical_normal_in_pointStabilizer radical_normalClosure_eq_top

end Atlas.F4
