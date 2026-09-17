import Atlas.Lattices.EisensteinBalancedNineShell
import Atlas.Lattices.EisensteinNormPatterns

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

theorem eisensteinBalancedNineParameter_normCount9 (p : EisensteinBalancedNineParameters) :
    eisensteinNormCount (eisensteinBalancedNineParameterShell p) 9=1 := by
  classical
  change (Finset.univ.filter (fun i => (eisensteinBalancedNineParameterVector p i).norm=9)).card=1
  have he : Finset.univ.filter (fun i => (eisensteinBalancedNineParameterVector p i).norm=9)=
      {p.2.1.val} := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,
      eisensteinBalancedNineParameter_coordinate_norm]
    by_cases hi : i=p.2.1.val
    · subst i
      simp [p.2.1.prop]
    · simp only [hi,ite_false,add_zero]
      split_ifs <;> norm_num
  rw [he,Finset.card_singleton]

end Atlas.Lattices
