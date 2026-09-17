import Atlas.Mathieu.Mathieu22PointStabilizer
import Atlas.Conway.Co3PointHeptadAction
import Atlas.Mathieu.GolayMarkedOctadTransitivity

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem co3_points_mathieu_transitive (a : Omega) (b c : Mathieu23Points a) :
    ∃ g : Mathieu23PointModel a,
      co3PointHeptadMap a g (Sum.inl b) = Sum.inl c := by
  letI := mathieu23_pretransitive a
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Mathieu23PointModel a) b c
  exact ⟨g,congrArg Sum.inl hg⟩

theorem co3_heptads_mathieu_transitive (a : Omega)
    (B C : {B // B ∈ mathieu23Blocks a}) :
    ∃ g : Mathieu23PointModel a,
      co3PointHeptadMap a g (Sum.inr B) = Sum.inr C := by
  obtain ⟨g,hg,hO⟩ := mathieu24_marked_octad_transitive {a}
    (insert a (mathieu23BlockLift a B.val)) (insert a (mathieu23BlockLift a C.val))
    (by simp) ((mathieu23Blocks_mem a B.val).mp B.prop)
    ((mathieu23Blocks_mem a C.val).mp C.prop) (by simp) (by simp)
  let p : Mathieu23PointModel a := ⟨g,hg a (by simp)⟩
  refine ⟨p,congrArg Sum.inr (Subtype.ext ?_)⟩
  ext i
  have h := Iff.of_eq (congrArg (fun T : Finset Omega => i.val ∈ T) hO)
  have hh : insert a (mathieu23BlockLift a (mathieu23PermuteBlock a p B.val)) =
      permuteBlock g.val (insert a (mathieu23BlockLift a B.val)) := by
    rw [mathieu23BlockLift_permute]
    have ha : g.val a = a := hg a (by simp)
    simp [permuteBlock,p,ha]
  rw [← hh] at h
  simpa [mathieu23BlockLift,(show i.val ≠ a from i.prop)] using h

theorem co3_mathieu_two_orbits (a : Omega) (p q : Co3PointHeptad a) :
    (∃ g : Mathieu23PointModel a, co3PointHeptadMap a g p = q) ↔
      (∃ b c, p = Sum.inl b ∧ q = Sum.inl c) ∨
      (∃ B C, p = Sum.inr B ∧ q = Sum.inr C) := by
  constructor
  · rintro ⟨g,rfl⟩
    cases p with
    | inl b => exact Or.inl ⟨b,g • b,rfl,rfl⟩
    | inr B => exact Or.inr ⟨B,_,rfl,rfl⟩
  · rintro (⟨b,c,rfl,rfl⟩ | ⟨B,C,rfl,rfl⟩)
    · exact co3_points_mathieu_transitive a b c
    · exact co3_heptads_mathieu_transitive a B C

end Atlas.Conway
