import Atlas.LinearGroups.Symplectic.BinaryOddRefinements
import Atlas.LinearGroups.Symplectic.Transvection
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace Atlas.Symplectic.BinaryException

def literal (a b c d : K) : V := Sum.elim ![a,b] ![c,d]

/-- The six actual odd-refinement parameters, with the original left/right marking. -/
def sixParameter : Fin 6 → V :=
  ![literal 1 0 1 0,literal 1 1 1 0,literal 1 0 1 1,
    literal 0 1 0 1,literal 1 1 0 1,literal 0 1 1 1]

theorem sixParameter_odd (i : Fin 6) : baseQuadratic (sixParameter i)=1 := by
  exact (by decide +kernel : ∀ i : Fin 6,baseQuadratic (sixParameter i)=1) i

def sixForms (i : Fin 6) : OddRefinement :=
  ⟨refinementOf (sixParameter i),(zeroCount_refinement_iff _).mpr (sixParameter_odd i)⟩

theorem sixForms_injective : Function.Injective sixForms := by
  intro i j h
  have h' := congrArg (fun Q : OddRefinement => parameterOf Q.val) h
  change parameterOf (refinementOf (sixParameter i))=parameterOf (refinementOf (sixParameter j)) at h'
  rw [parameter_refinement,parameter_refinement] at h'
  exact (by decide +kernel : Function.Injective sixParameter) h'

/-- The displayed six refinements exhaust the genuine six-point geometry. -/
def sixFormsEquiv : Fin 6 ≃ OddRefinement :=
  Equiv.ofBijective sixForms ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨sixForms_injective,by rw [card_oddRefinement]; simp⟩)

/-- Fixing these actual six quadratic forms forces all four vector coordinates to be fixed. -/
instance oddRefinement_faithful : FaithfulSMul (Sp 2 K) OddRefinement := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hginv : g⁻¹=1 := by
    apply ext_action
    intro x
    rw [one_smul]
    have H (i : Fin 6) := congrArg (fun Q : OddRefinement => Q.val.val x) (hg (sixForms i))
    have h0 := H 0
    have h1 := H 1
    have h2 := H 2
    have h3 := H 3
    have h4 := H 4
    have h5 := H 5
    simp only [oddRefinementAction_apply] at h0 h1 h2 h3 h4 h5
    simp [sixForms,sixParameter,literal,refinementOf,baseQuadratic,form_apply,Fin.sum_univ_two]
      at h0 h1 h2 h3 h4 h5
    funext s
    rcases s with i|i <;> fin_cases i
    · change (g⁻¹ • x) (.inl 0)=x (.inl 0)
      linear_combination h5-h3
    · change (g⁻¹ • x) (.inl 1)=x (.inl 1)
      linear_combination h2-h0
    · change (g⁻¹ • x) (.inr 0)=x (.inr 0)
      linear_combination h3-h4
    · change (g⁻¹ • x) (.inr 1)=x (.inr 1)
      linear_combination h0-h1
  exact inv_eq_one.mp hginv

end Atlas.Symplectic.BinaryException
