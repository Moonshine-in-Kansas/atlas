import Atlas.Lattices.EisensteinBalancedNineInjective

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
attribute [local instance] Classical.propDecidable

def eisensteinBalancedNineVectors : Finset (EisensteinShell 6) :=
  Finset.univ.image eisensteinBalancedNineParameterShell

theorem eisensteinBalancedNineParameterShell_injective :
    Function.Injective eisensteinBalancedNineParameterShell := by
  intro p q h
  exact eisensteinBalancedNineParameterVector_injective (congrArg (fun x => x.val.val) h)

/-- Exactly1924560 actual norm-six lattice vectors arise from the balanced
norm-nine-plus-hexad construction. -/
theorem eisensteinBalancedNineVectors_card : eisensteinBalancedNineVectors.card=1924560 := by
  rw [eisensteinBalancedNineVectors,Finset.card_image_of_injective _
    eisensteinBalancedNineParameterShell_injective,Finset.card_univ,← Nat.card_eq_fintype_card]
  exact eisensteinBalancedNineParameters_card

end Atlas.Lattices
