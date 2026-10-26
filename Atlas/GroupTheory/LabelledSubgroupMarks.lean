import Atlas.GroupTheory.MarkedReducedWordEvaluation
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Tauto

/-! Marks retain both an explicit label and a literal subgroup. The product
of the permutation group with the existing group is only bookkeeping: no
faithfulness or identification of a normalizer quotient is assumed. -/
namespace Atlas.GroupTheory

variable {I G A : Type*} [Group G] [Group A]

def conjugateSubgroup (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

@[simp] theorem conjugateSubgroup_one (H : Subgroup G) :
    conjugateSubgroup 1 H = H := by
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
  rw [conjugateSubgroup, h, Subgroup.map_id]

theorem conjugateSubgroup_mul (g h : G) (H : Subgroup G) :
    conjugateSubgroup (g * h) H =
      conjugateSubgroup g (conjugateSubgroup h H) := by
  unfold conjugateSubgroup
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev, mul_assoc]

theorem conjugateSubgroup_range (g : G) (f : A →* G) :
    conjugateSubgroup g f.range = ((MulAut.conj g).toMonoidHom.comp f).range :=
  MonoidHom.map_range _ _

/-- Reparameterizing a root homomorphism by any surjection preserves its
literal range. This will account for the sign -t without discarding labels. -/
theorem conjugateSubgroup_range_eq_of_surjective
    (g : G) (f h : A →* G) (e : A → A) (he : Function.Surjective e)
    (hconj : ∀ a, g * f a * g⁻¹ = h (e a)) :
    conjugateSubgroup g f.range = h.range := by
  rw [conjugateSubgroup_range]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e a, (hconj a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := he a
    exact ⟨b, hconj b⟩

/-- Simultaneous permutation of root labels and conjugation of actual groups. -/
def labelledSubgroupAction : (Equiv.Perm I × G) →* Function.End (I × Subgroup G) where
  toFun g m := (g.1 m.1, conjugateSubgroup g.2 m.2)
  map_one' := by
    funext m
    apply Prod.ext
    · rfl
    · exact conjugateSubgroup_one m.2
  map_mul' g h := by
    funext m
    apply Prod.ext
    · rfl
    · exact conjugateSubgroup_mul g.2 h.2 m.2

@[simp] theorem labelledSubgroupAction_apply (g : Equiv.Perm I × G)
    (m : I × Subgroup G) :
    labelledSubgroupAction g m = (g.1 m.1, conjugateSubgroup g.2 m.2) := rfl

end Atlas.GroupTheory

namespace Atlas.GroupTheory.ReducedWords
variable {I G Mark : Type*} [Monoid G]

theorem markedWordSet_two_of_fixed (t : I → G) (act : G →* Function.End Mark)
    (mark : I → Mark) (i j : I)
    (hij : act (t i) (mark j) = mark j)
    (hji : act (t j) (mark i) = mark i) :
    markedWordSet t act mark [i,j] = markedWordSet t act mark [j,i] := by
  simp only [markedWordSet]
  repeat' first
    | erw [Set.image_union]
    | erw [Set.image_empty]
    | erw [Set.image_singleton]
    | rw [Set.union_empty]
  simp only [hij, hji]
  exact Set.union_comm _ _

theorem markedWordSet_three_of_transport (t : I → G)
    (act : G →* Function.End Mark) (mark : I → Mark) (i j : I)
    (hmiddle : act (t i) (mark j) = act (t j) (mark i))
    (hleft : act (t i) (act (t j) (mark i)) = mark j)
    (hright : act (t j) (act (t i) (mark j)) = mark i) :
    markedWordSet t act mark [i,j,i] = markedWordSet t act mark [j,i,j] := by
  simp only [markedWordSet]
  repeat' first
    | erw [Set.image_union]
    | erw [Set.image_empty]
    | erw [Set.image_singleton]
    | rw [Set.union_empty]
  simp only [hleft, hright]
  rw [hmiddle]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff]
  tauto

/-- The two middle marks are fixed, and squares fix the opposite endpoint.
These are explicit local hypotheses, not a generic coherence assertion. -/
theorem markedWordSet_four_of_middle_fixed (t : I → G)
    (act : G →* Function.End Mark) (mark : I → Mark) (i j : I)
    (hshort : act (t i) (act (t j) (mark i)) = act (t j) (mark i))
    (hlong : act (t j) (act (t i) (mark j)) = act (t i) (mark j))
    (hisq : act (t i) (act (t i) (mark j)) = mark j)
    (hjsq : act (t j) (act (t j) (mark i)) = mark i) :
    markedWordSet t act mark [i,j,i,j] = markedWordSet t act mark [j,i,j,i] := by
  simp only [markedWordSet]
  repeat' first
    | erw [Set.image_union]
    | erw [Set.image_empty]
    | erw [Set.image_singleton]
    | rw [Set.union_empty]
  simp only [hshort, hlong, hisq, hjsq]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff]
  tauto

end Atlas.GroupTheory.ReducedWords
