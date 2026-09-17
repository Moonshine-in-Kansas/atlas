import Atlas.LinearGroups.Orthogonal.B1SingularFaithful
import Atlas.LinearGroups.Orthogonal.EvenBSingularPoints
import Atlas.LinearGroups.Orthogonal.SingularGeometryOddB
import Atlas.LinearGroups.Orthogonal.RootNormalGenerationLines
import Atlas.LinearGroups.Orthogonal.CoordinateRootGenerationB1

/-! # Uniform actual B singular geometry and coordinate generation

The singular action remains on the original quadratic-form lines. Even-field
primitivity is transported through the actual square-root point equivalence;
odd rank two uses complement line transport, never false vector transitivity.
-/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem B_faithful_all_rank (n : ℕ) (hn : 1 ≤ n) :
    FaithfulSMul (B n F) (SingularPoints (formB n F)) := by
  by_cases h : n = 1
  · subst n
    exact B1_projective_singular_faithful
  · exact B_faithful n (by omega)

theorem B_coordinate_roots_generate_all_rank (n : ℕ) (hn : 1 ≤ n) :
    coordinateRootSubgroupB (F := F) n = elementarySubgroup (formB n F) :=
  coordinateRootSubgroupB_eq_elementary_of_pos n hn

variable [Finite F]

theorem B_elementary_singular_line_transport_all_rank (n : ℕ) (hn : 1 ≤ n)
    (u v : VectorB n F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : formB n F u = 0) (hqv : formB n F v = 0) :
    ∃ g : O_B n F, g ∈ elementarySubgroup (formB n F) ∧
      ∃ c : F, c ≠ 0 ∧ g.val u = c • v := by
  by_cases hn1 : n = 1
  · subst n
    exact elementaryB1_singular_line_transport u v hu hv hqu hqv
  · by_cases h2 : (2 : F) = 0
    · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      obtain ⟨g,hg,hgu⟩ := evenB_elementary_singular_transport u v hu hv hqu hqv
      exact ⟨g,hg,1,one_ne_zero,by simpa only [one_smul] using hgu⟩
    · obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n-2,by omega⟩
      obtain ⟨g,hg,hgu⟩ := elementaryB_singular_transport k h2 u v hu hv hqu hqv
      exact ⟨g,hg,1,one_ne_zero,by simpa only [one_smul] using hgu⟩

theorem B_elementary_transitive_all_rank (n : ℕ) (hn : 1 ≤ n) :
    MulAction.IsPretransitive (elementarySubgroup (formB n F)) (SingularPoints (formB n F)) where
  exists_smul_eq p q := by
    obtain ⟨g,hg,c,hc,hgq⟩ := B_elementary_singular_line_transport_all_rank n hn
      p.val.rep q.val.rep p.val.rep_nonzero q.val.rep_nonzero p.prop q.prop
    exact ⟨⟨g,hg⟩,singularPoints_smul_eq_of_scaled_rep _ g p q c hgq⟩

theorem B_transitive_all_rank (n : ℕ) (hn : 1 ≤ n) :
    MulAction.IsPretransitive (B n F) (SingularPoints (formB n F)) := by
  letI := B_elementary_transitive_all_rank (F := F) n hn
  exact projectiveSingular_pretransitive _

theorem B_elementary_primitive_all_char (n : ℕ) (hn : 2 ≤ n) :
    MulAction.IsPreprimitive (elementarySubgroup (formB n F)) (SingularPoints (formB n F)) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact evenB_elementary_primitive hn
  · obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n-2,by omega⟩
    exact singularPointsB_primitive_rank_two_up k h2

theorem B_primitive_all_char (n : ℕ) (hn : 2 ≤ n) :
    MulAction.IsPreprimitive (B n F) (SingularPoints (formB n F)) := by
  letI := B_elementary_primitive_all_char (F := F) n hn
  let f : SingularPoints (formB n F) →ₑ[projectiveElementaryMap (formB n F)]
      SingularPoints (formB n F) := { toFun := id, map_smul' := fun _ _ => rfl }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

theorem B_roots_normal_generate_all_rank (n : ℕ) (hn : 1 ≤ n)
    (p : SingularPoints (formB n F)) :
    Subgroup.normalClosure (projectiveRootSubgroup (formB n F) p : Set (B n F)) = ⊤ := by
  let Q := formB n F
  have h := Subgroup.map_normalClosure
    (((rootSubgroup Q p.val.rep p.prop).subgroupOf (elementarySubgroup Q)) : Set _)
    (projectiveElementaryMap Q) (projectiveElementaryMap_surjective Q)
  rw [root_normalClosure_eq_top_of_line_transport Q p.val.rep p.prop
    (fun u hu hqu => B_elementary_singular_line_transport_all_rank n hn
      p.val.rep u p.val.rep_nonzero hu p.prop hqu)] at h
  rw [Subgroup.map_top_of_surjective _ (projectiveElementaryMap_surjective Q)] at h
  exact h.symm
end Atlas.Orthogonal
