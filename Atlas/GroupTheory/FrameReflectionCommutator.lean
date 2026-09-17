import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.GroupAction.Basic

namespace Atlas.GroupTheory
open scoped commutatorElement

/-- Three commuting involutions with product one give an explicit frame
commutator whenever a group element takes the first to the second. -/
theorem frame_involution_commutator {G : Type*} [Group G] (a b c d : G)
    (ha : a*a=1) (hb : b*b=1) (hc : c*c=1)
    (hab : a*b=b*a) (hprod : a*b*c=1) (hd : d*a*d⁻¹=b) : ⁅d,a⁆=c := by
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right ha
  have he : a*b=c := (mul_eq_one_iff_eq_inv.mp hprod).trans
    (inv_eq_of_mul_eq_one_right hc)
  rw [commutatorElement_def,hd,hai,← hab,he]

/-- A conjugation-equivariant generating family in a transitive geometry is
perfect once a single member is an explicit commutator. -/
theorem perfect_of_transitive_commutator_family {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (r : X → G)
    (hcov : ∀ g x,g*r x*g⁻¹=r (g • x))
    (hgen : Subgroup.closure (Set.range r)=⊤)
    (x : X) (a b : G) (hab : ⁅a,b⁆=r x) : Group.IsPerfect G := by
  have hr : r x∈commutator G := by
    rw [← hab]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hle : Subgroup.closure (Set.range r)≤commutator G := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨y,rfl⟩
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
    rw [← hg,← hcov]
    exact Subgroup.Normal.conj_mem inferInstance _ hr g
  exact ⟨top_unique (hgen ▸ hle)⟩

end Atlas.GroupTheory
