import Atlas.LinearGroups.Orthogonal.ElementaryNormal
import Atlas.LinearAlgebra.QuadraticSplit
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Actual abelian Siegel subgroups and their parameter kernels -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (u : V) (hu : Q u = 0)

abbrev rootParameterSpace := (Q.polarBilin u).ker

def rootParameterHom : Multiplicative (rootParameterSpace Q u) →* isometrySubgroup Q where
  toFun v := siegelElement Q u v.toAdd.val hu v.toAdd.prop
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact siegel_zero Q u x
  map_mul' v w := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact (siegel_add Q u v.toAdd.val w.toAdd.val x hu v.toAdd.prop w.toAdd.prop).symm

/-- The actual local subgroup, defined inside the full quadratic isometry group. -/
def rootSubgroup : Subgroup (isometrySubgroup Q) := (rootParameterHom Q u hu).range

theorem rootSubgroup_le_elementary : rootSubgroup Q u hu ≤ elementarySubgroup Q := by
  rintro g ⟨v, rfl⟩
  exact siegelElement_mem _ _ _ _ _

instance rootSubgroup_isMulCommutative : IsMulCommutative (rootSubgroup Q u hu) :=
  Function.Surjective.isMulCommutative
    (rootParameterHom Q u hu).rangeRestrict_surjective inferInstance

/-- The first isomorphism theorem on the actual parameter homomorphism. -/
def rootParameterQuotientEquiv :
    (Multiplicative (rootParameterSpace Q u) ⧸ (rootParameterHom Q u hu).ker) ≃*
      rootSubgroup Q u hu := QuotientGroup.quotientKerEquivRange _

variable (f : V) (huf : Q.polarBilin u f = 1)

include huf in
/-- Only multiples of the singular direction give the identity transformation. -/
theorem rootParameter_kernel (v : rootParameterSpace Q u) :
    rootParameterHom Q u hu (Multiplicative.ofAdd v) = 1 ↔ ∃ c : F, v.val = c • u := by
  constructor
  · intro h
    have he := congrArg (fun g : isometrySubgroup Q => g.val f) h
    have hfu : Q.polarBilin f u = 1 := (polar_swap Q f u).trans huf
    change siegel Q u v.val f = f at he
    simp only [siegel, hfu, one_smul, mul_one] at he
    refine ⟨Q.polarBilin f v.val - Q v.val, ?_⟩
    rw [sub_smul]
    have := congrArg (fun x : V => x-f+v.val) he
    convert this.symm using 1 <;> abel
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change siegel Q u v.val x = x
    rw [hc]
    have h := siegel_parameter_mod_line Q u 0 x c hu (by simp)
    simpa only [zero_add, siegel_zero] using h

end Atlas.Orthogonal
