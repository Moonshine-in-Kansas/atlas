import Atlas.Conway.McLTriangleCounts

noncomputable section
set_option maxRecDepth 4096
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem mcl_base_triangle_orbit_card :
    Nat.card (MulAction.orbit McLModel mclBaseTriangle) = 2025 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup McLModel mclBaseTriangle)
  rw [Nat.card_prod,mcl_triangle_stabilizer_card,mcl_order] at h
  have hn : (898128000 : ℕ) = 2025*443520 := by norm_num
  rw [hn] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 443520) h

theorem mcl_base_triangle_orbit_eq_univ :
    MulAction.orbit McLModel mclBaseTriangle = Set.univ := by
  apply (Set.eq_univ_iff_ncard _).mpr
  rw [← Nat.card_coe_set_eq]
  rw [mcl_base_triangle_orbit_card,mcl_triangles_card]

theorem mcl_triangles_transitive : MulAction.IsPretransitive McLModel McLTriangles := by
  constructor
  intro x y
  have hx : x ∈ MulAction.orbit McLModel mclBaseTriangle := by
    rw [mcl_base_triangle_orbit_eq_univ]; trivial
  have hy : y ∈ MulAction.orbit McLModel mclBaseTriangle := by
    rw [mcl_base_triangle_orbit_eq_univ]; trivial
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hx
  obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hy
  exact ⟨h*g⁻¹,by rw [← hg,mul_smul,inv_smul_smul,hh]⟩

end Atlas.Conway
