import Atlas.LinearGroups.Symplectic.RefinementAction
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
namespace Atlas.Symplectic.BinaryException
abbrev K := ZMod 2
abbrev V := Vector 2 K

/-- Quadratic refinements of the actual four-dimensional alternating form. -/
abbrev Refinement := FormRefinement 2 K

def baseQuadratic (x : V) : K := x (.inl 0)*x (.inr 0)+x (.inl 1)*x (.inr 1)

theorem baseQuadratic_polar (x y : V) :
    baseQuadratic (x+y)=baseQuadratic x+baseQuadratic y+form x y := by
  simp [baseQuadratic,form_apply,Fin.sum_univ_two]
  ring_nf
  simp only [CharTwo.sub_eq_add]

def refinementOf (a : V) : Refinement :=
  ⟨fun x => baseQuadratic x+form x a,by simp [baseQuadratic],by
    intro x y
    dsimp only
    rw [baseQuadratic_polar,map_add,LinearMap.add_apply]
    ring⟩

def parameterOf (Q : Refinement) : V :=
  Sum.elim (fun i => Q.val (f i)) (fun i => Q.val (e i))

theorem refinement_smul (Q : Refinement) (c : K) (x : V) : Q.val (c • x)=c*Q.val x := by
  fin_cases c
  · change Q.val ((0 : K) • x) = (0 : K)*Q.val x
    rw [zero_smul,Q.prop.1,zero_mul]
  · change Q.val ((1 : K) • x) = (1 : K)*Q.val x
    rw [one_smul,one_mul]

theorem coordinates (x : V) :
    x=x (.inl 0) • e 0+x (.inl 1) • e 1+x (.inr 0) • f 0+x (.inr 1) • f 1 := by
  funext i
  rcases i with i|i <;> fin_cases i <;> simp [e,f,Pi.single_apply]

theorem refinement_reconstruction (Q : Refinement) : refinementOf (parameterOf Q)=Q := by
  apply Subtype.ext
  funext x
  change baseQuadratic x+form x (parameterOf Q)=Q.val x
  conv_rhs => rw [coordinates x]
  simp only [Q.prop.2,refinement_smul]
  simp [baseQuadratic,parameterOf,form_apply,Fin.sum_univ_two,e,f,Pi.single_apply]
  ring_nf
  simp only [CharTwo.sub_eq_add]

theorem parameter_refinement (a : V) : parameterOf (refinementOf a)=a := by
  funext i
  rcases i with i|i <;> fin_cases i <;>
    simp [parameterOf,refinementOf,baseQuadratic,form_apply,Fin.sum_univ_two,e,f,Pi.single_apply]

/-- All refinements, without omitting a polar-compatible quadratic form. -/
def refinementEquiv : V ≃ Refinement where
  toFun := refinementOf
  invFun := parameterOf
  left_inv := parameter_refinement
  right_inv := refinement_reconstruction

end Atlas.Symplectic.BinaryException
