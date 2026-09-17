import Atlas.LinearGroups.Orthogonal.BGeometryInterface
import Atlas.LinearGroups.Orthogonal.ProjectiveEvenB

/-! # Actual singular-vector transport in characteristic-two B spaces -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F] [CharP F 2]

theorem evenB_singular_first_ne_zero (u : VectorB n F) (hu : u ≠ 0)
    (hq : formB n F u = 0) : u.1 ≠ 0 := by
  intro hz
  have hs : u.2 ^ 2 = 0 := by simpa only [formB_apply,hz,map_zero,zero_add] using hq
  have hs' : u.2 = 0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hs
  exact hu (Prod.ext hz hs')

theorem evenB_singular_eq_of_first_eq (u v : VectorB n F)
    (hu : formB n F u = 0) (hv : formB n F v = 0) (hfirst : u.1 = v.1) : u = v := by
  apply Prod.ext hfirst
  have hs : u.2^2 = v.2^2 := by
    rw [formB_apply,hfirst] at hu
    rw [formB_apply] at hv
    exact add_left_cancel (hu.trans hv.symm)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h|h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

variable [PerfectRing F 2]

theorem evenB_elementary_singular_transport (u v : VectorB n F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : formB n F u = 0) (hqv : formB n F v = 0) :
    ∃ g : O_B n F, g ∈ elementarySubgroup (formB n F) ∧ g.val u = v := by
  obtain ⟨a,_,ha⟩ := Atlas.Symplectic.exists_generated_send
    (evenB_singular_first_ne_zero u hu hqu) (evenB_singular_first_ne_zero v hv hqv)
  obtain ⟨g,hg⟩ := evenProjection_surjective a
  refine ⟨g,by rw [even_elementary_eq_top]; trivial,?_⟩
  apply evenB_singular_eq_of_first_eq _ v ((g.prop u).trans hqu) hqv
  rw [even_first]
  exact (evenProjection_apply g u.1).symm.trans (by rw [hg]; exact ha)

theorem evenB_elementary_pretransitive :
    MulAction.IsPretransitive (elementarySubgroup (formB n F)) (SingularPoints (formB n F)) :=
  singularPoints_pretransitive _ evenB_elementary_singular_transport

theorem evenB_projective_pretransitive :
    MulAction.IsPretransitive (B n F) (SingularPoints (formB n F)) := by
  letI := evenB_elementary_pretransitive (n := n) (F := F)
  exact projectiveSingular_pretransitive _

theorem evenB_roots_normal_generate (p : SingularPoints (formB n F)) :
    Subgroup.normalClosure (projectiveRootSubgroup (formB n F) p : Set (B n F)) = ⊤ :=
  projectiveRoot_normalClosure_eq_top _ p (fun u hu hqu =>
    evenB_elementary_singular_transport p.val.rep u p.val.rep_nonzero hu p.prop hqu)

end Atlas.Orthogonal
