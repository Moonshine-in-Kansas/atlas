import Atlas.Conway.EisensteinBalancedClassFibers

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def eisensteinBalancedClasses : Finset EisensteinClasses :=
  Finset.univ.image eisensteinBalancedParameterClass

theorem eisensteinBalancedClasses_card : eisensteinBalancedClasses.card=35640 := by
  have h := Finset.card_eq_sum_card_image (f := eisensteinBalancedParameterClass) Finset.univ
  have hf (C : EisensteinClasses) (hC : C ∈ eisensteinBalancedClasses) :
      (Finset.univ.filter (fun p => eisensteinBalancedParameterClass p=C)).card=9 := by
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hC
    rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card]
    exact eisensteinBalancedParameterClass_fiber_card p
  change Fintype.card EisensteinBalancedParameters =
    ∑ C ∈ eisensteinBalancedClasses,(Finset.univ.filter (fun p => eisensteinBalancedParameterClass p=C)).card at h
  rw [← Nat.card_eq_fintype_card,eisensteinBalancedParameters_card] at h
  have hh : (∑ C ∈ eisensteinBalancedClasses,
      (Finset.univ.filter (fun p => eisensteinBalancedParameterClass p=C)).card)=
        eisensteinBalancedClasses.card*9 := by
    simp_rw [Finset.sum_congr rfl hf]
    simp
  rw [hh] at h
  omega

theorem eisensteinBalancedParameterClass_nonzero (p : EisensteinBalancedParameters) :
    eisensteinBalancedParameterClass p≠0 := by
  intro h
  have hm := (Submodule.Quotient.mk_eq_zero _).mp h
  have hx : eisensteinBalancedPhasedLatticeVector p.1 p.2.1 p.2.2≠0 := by
    intro he
    have hn := eisensteinBalancedPhasedVector_norm p.1 p.2.1 p.2.2
    rw [he] at hn
    norm_num [eisensteinNorm,eisensteinBilinear,eisensteinHermitian,eisensteinReal] at hn
  have hn := eisensteinNorm_theta_minimum _ hm hx
  rw [eisensteinBalancedPhasedVector_norm] at hn
  norm_num at hn

end Atlas.Conway
