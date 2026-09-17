import Atlas.Conway.EisensteinBalancedNineVectorAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def eisensteinBalancedNineParameterFrame (p : EisensteinBalancedNineParameters) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinBalancedNineParameterShell p)

def eisensteinBalancedNineFamily : Finset EisensteinFrame :=
  Finset.univ.image eisensteinBalancedNineParameterFrame

theorem eisensteinBalancedNineParameterFrame_mem (p : EisensteinBalancedNineParameters) :
    eisensteinBalancedNineParameterFrame p ∈ eisensteinBalancedNineFamily :=
  Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩

theorem eisensteinBalancedNineFamily_transitive (F G : EisensteinFrame)
    (hF : F ∈ eisensteinBalancedNineFamily) (hG : G ∈ eisensteinBalancedNineFamily) :
    ∃ g : eisensteinCoordinateFrameStabilizer,g.val • F=G := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hG
  obtain ⟨g,hg⟩ := eisensteinBalancedNineVectors_transitive p q
  refine ⟨g,?_⟩
  simp only [eisensteinBalancedNineParameterFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  exact hg

theorem eisensteinBalancedNineFamily_invariant (g : eisensteinCoordinateFrameStabilizer)
    (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedNineFamily) :
    g.val • F ∈ eisensteinBalancedNineFamily := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨q,hq⟩ := eisensteinBalancedNineParameter_action g p
  refine Finset.mem_image.mpr ⟨q,Finset.mem_univ _,?_⟩
  simp only [eisensteinBalancedNineParameterFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  exact hq.symm

theorem eisensteinBalancedNineFamily_orbit (F : EisensteinFrame) (hF : F ∈ eisensteinBalancedNineFamily) :
    MulAction.orbit eisensteinCoordinateFrameStabilizer F=(eisensteinBalancedNineFamily : Set EisensteinFrame) := by
  ext G
  constructor
  · rintro ⟨g,rfl⟩
    exact eisensteinBalancedNineFamily_invariant g F hF
  · intro hG
    obtain ⟨g,hg⟩ := eisensteinBalancedNineFamily_transitive F G hF hG
    exact ⟨g,hg⟩

end Atlas.Conway
