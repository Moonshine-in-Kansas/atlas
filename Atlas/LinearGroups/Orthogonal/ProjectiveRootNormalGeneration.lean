import Atlas.LinearGroups.Orthogonal.RootNormalGeneration
import Atlas.LinearGroups.Orthogonal.RootPointStabilizer
import Atlas.LinearGroups.Orthogonal.SingularProjectiveAction
import Atlas.LinearGroups.Orthogonal.ElementaryTransitivityAllChar

/-! # Actual root images in the scalar quotient and their normal generation -/
noncomputable section
namespace Atlas.Orthogonal
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (p : SingularPoints Q)

def projectiveRootSubgroup : Subgroup (ProjectiveElementary Q) :=
  ((rootSubgroup Q p.val.rep p.prop).subgroupOf (elementarySubgroup Q)).map
    (projectiveElementaryMap Q)

instance projectiveRoot_commutative : IsMulCommutative (projectiveRootSubgroup Q p) :=
  inferInstanceAs (IsMulCommutative (((rootSubgroup Q p.val.rep p.prop).subgroupOf
    (elementarySubgroup Q)).map (projectiveElementaryMap Q)))

theorem projectiveRoot_le_point_stabilizer : projectiveRootSubgroup Q p ≤
    MulAction.stabilizer (ProjectiveElementary Q) p := by
  rintro g ⟨r,hr,rfl⟩
  exact elementaryRoot_le_point_stabilizer Q p hr

theorem projectiveRoot_normal_point_stabilizer :
    ((projectiveRootSubgroup Q p).subgroupOf
      (MulAction.stabilizer (ProjectiveElementary Q) p)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (projectiveRoot_le_point_stabilizer Q p)).mpr
  intro r g hr hg
  obtain ⟨a,ha,rfl⟩ := hr
  obtain ⟨b,rfl⟩ := projectiveElementaryMap_surjective Q g
  have hb : b ∈ MulAction.stabilizer (elementarySubgroup Q) p := hg
  have hn := (Subgroup.normal_subgroupOf_iff (elementaryRoot_le_point_stabilizer Q p)).mp
    (elementaryRoot_normal_point_stabilizer Q p) a b ha hb
  exact ⟨b*a*b⁻¹,hn,by simp only [map_mul,map_inv]⟩

theorem projectiveRoot_normalClosure_eq_top
    (ht : ∀ u : V, u ≠ 0 → Q u = 0 →
      ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val p.val.rep = u) :
    Subgroup.normalClosure (projectiveRootSubgroup Q p : Set (ProjectiveElementary Q)) = ⊤ := by
  have h := Subgroup.map_normalClosure
    (((rootSubgroup Q p.val.rep p.prop).subgroupOf (elementarySubgroup Q)) : Set _)
    (projectiveElementaryMap Q) (projectiveElementaryMap_surjective Q)
  rw [root_normalClosure_eq_top Q p.val.rep p.prop ht] at h
  rw [Subgroup.map_top_of_surjective _ (projectiveElementaryMap_surjective Q)] at h
  exact h.symm

theorem projectiveRootD_normalClosure_eq_top (n : ℕ)
    (p : SingularPoints (formD (n+2) F)) :
    Subgroup.normalClosure (projectiveRootSubgroup (formD (n+2) F) p :
      Set (ProjectiveElementary (formD (n+2) F))) = ⊤ :=
  projectiveRoot_normalClosure_eq_top _ p (fun u hu hqu =>
    elementaryD_singular_transport_all_char n p.val.rep u p.val.rep_nonzero hu p.prop hqu)

end Atlas.Orthogonal
