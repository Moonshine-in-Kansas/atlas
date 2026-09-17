import Atlas.LinearGroups.Orthogonal.BFamily
import Atlas.LinearGroups.Orthogonal.ProjectiveRootNormalGeneration
import Atlas.LinearGroups.Orthogonal.SingularPrimitiveB

/-! # Public B singular-line and root interfaces with their verified scopes

Faithfulness holds in every characteristic. The transport and normal-generation
interfaces below concern odd characteristic. They are actual group-action facts,
not an unfolding of the definition of the elementary subgroup.
-/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem B_faithful (n : ℕ) (hn : 2 ≤ n) :
    FaithfulSMul (B n F) (SingularPoints (formB n F)) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact projectiveSingularB_faithful k

theorem B_odd_transitive (n : ℕ) (hn : 2 ≤ n) (h2 : (2 : F) ≠ 0) :
    MulAction.IsPretransitive (B n F) (SingularPoints (formB n F)) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact projectiveSingularB_pretransitive k h2

theorem B_odd_elementary_primitive (n : ℕ) (hn : 3 ≤ n) (h2 : (2 : F) ≠ 0) :
    MulAction.IsPreprimitive (elementarySubgroup (formB n F)) (SingularPoints (formB n F)) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  exact singularPointsB_primitive k h2

theorem B_roots_abelian (n : ℕ) (p : SingularPoints (formB n F)) :
    IsMulCommutative (projectiveRootSubgroup (formB n F) p) := inferInstance

theorem B_roots_normal_in_stabilizer (n : ℕ) (p : SingularPoints (formB n F)) :
    ((projectiveRootSubgroup (formB n F) p).subgroupOf
      (MulAction.stabilizer (B n F) p)).Normal :=
  projectiveRoot_normal_point_stabilizer _ p

theorem B_odd_roots_normal_generate (n : ℕ) (hn : 2 ≤ n) (h2 : (2 : F) ≠ 0)
    (p : SingularPoints (formB n F)) :
    Subgroup.normalClosure (projectiveRootSubgroup (formB n F) p : Set (B n F)) = ⊤ := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact projectiveRoot_normalClosure_eq_top _ p (fun u hu hqu =>
    elementaryB_singular_transport k h2 p.val.rep u p.val.rep_nonzero hu p.prop hqu)
end Atlas.Orthogonal
