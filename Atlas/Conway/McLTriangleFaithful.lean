import Atlas.Conway.McLTrianglePrimitivity
import Atlas.Conway.McLStronglyRegular
import Atlas.GroupTheory.SimpleStabilizerFaithful

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

theorem mcl_triangle_stabilizer_graph_orbit (c : McLPointLabels) :
    orbit McLTriangleStabilizer (mclWittVector (Sum.inl c)) =
      Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d)) := by
  rw [← mcl_point_family_orbit c]
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨h,rfl⟩ := mclMathieuTriangleEquiv.surjective g
    exact mem_orbit_iff.mpr ⟨h,rfl⟩
  · rintro ⟨g,rfl⟩
    exact mem_orbit_iff.mpr ⟨mclMathieuTriangleEquiv g,rfl⟩

theorem mcl_triangle_stabilizer_not_normal : ¬ McLTriangleStabilizer.Normal := by
  intro hn
  letI := hn
  letI := mcl_graph_transitive
  let c := mclBaseGraphLabel
  have hB : IsBlock McLModel (orbit McLTriangleStabilizer (mclWittVector (Sum.inl c))) :=
    IsBlock.orbit_of_normal _
  have hd := hB.ncard_dvd_card ⟨_,mem_orbit_self _⟩
  rw [mcl_triangle_stabilizer_graph_orbit] at hd
  change Nat.card (Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d))) ∣
    Nat.card McLGraphPoints at hd
  rw [mcl_point_family_card,mcl_graph_card] at hd
  exact (by decide : ¬22 ∣ 275) hd

theorem mcl_triangles_faithful : FaithfulSMul McLModel McLTriangles := by
  letI := mcl_triangle_stabilizer_simple
  exact Atlas.GroupTheory.faithful_of_simple_stabilizer_not_normal mclBaseTriangle
    mcl_triangle_stabilizer_not_normal

end Atlas.Conway
