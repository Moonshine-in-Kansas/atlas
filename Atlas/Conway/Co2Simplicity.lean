import Atlas.Conway.Co2LineFaithfulness
import Atlas.Sporadic.Conway2Generation
import Atlas.GroupTheory.IwasawaStabilizer

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

theorem co2Signs_le_local : co2Signs ≤ Atlas.Sporadic.Conway2.LocalGroup := by
  rintro g ⟨h,_,rfl⟩
  exact h.prop

theorem co2Signs_subgroupOf :
    co2Signs.subgroupOf Atlas.Sporadic.Conway2.LocalGroup = Atlas.Sporadic.Conway2.signs := by
  change co2Signs.comap (orthogonalLineStabilizer ((0,0),0) ((0,0),1)).subtype =
    orthogonalLineSigns ((0,0),0)
      ⟨((0,0),1),by change ((0,0),1) ≠ ((0,0),0); decide⟩
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨h,hh,he⟩
    have he' : h = g := Subtype.ext he
    rwa [← he']
  · intro hg
    exact ⟨g,hg,rfl⟩

theorem co2Signs_abelian : IsMulCommutative co2Signs := by
  refine ⟨⟨fun g h => ?_⟩⟩
  obtain ⟨g',hg,he⟩ := g.prop
  obtain ⟨h',hh,hf⟩ := h.prop
  apply Subtype.ext
  change g.val*h.val = h.val*g.val
  rw [← he,← hf]
  exact congrArg (fun k : Atlas.Sporadic.Conway2.LocalGroup => k.val)
    (congrArg Subtype.val (Atlas.Sporadic.Conway2.signs_commute ⟨g',hg⟩ ⟨h',hh⟩))

theorem co2_simple : IsSimpleGroup Co2MarkedModel := by
  have := co2_lines_faithful
  have := Atlas.Sporadic.Conway2.primitive
  have := Atlas.Sporadic.Conway2.perfect
  have : Nontrivial Co2MarkedModel := by
    obtain ⟨g,h,hh⟩ := co2_noncommuting_pair
    exact ⟨⟨g*h,h*g,hh⟩⟩
  apply Atlas.GroupTheory.iwasawa_stabilizer_simple Atlas.Sporadic.Conway2.basePoint co2Signs
  · rw [Atlas.Sporadic.Conway2.full_point_stabilizer]
    exact co2Signs_le_local
  · rw [Atlas.Sporadic.Conway2.full_point_stabilizer,co2Signs_subgroupOf]
    exact Atlas.Sporadic.Conway2.signs_normal
  · exact co2Signs_abelian
  · exact co2Signs_normalClosure

end Atlas.Conway
