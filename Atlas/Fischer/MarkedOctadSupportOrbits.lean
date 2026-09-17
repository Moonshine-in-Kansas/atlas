import Atlas.Fischer.MathieuOctadLocalTransport
import Atlas.Mathieu.GolayMarkedOctadTransitivity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Actual Mathieu transport of octads fixing the prescribed inside markings
pointwise and a prescribed exterior point. -/
theorem mathieu_marked_octad_transitive (S : Finset Omega) (hS : S.card≤2)
    (x : Omega) (O P : Octad) (hSO : S ⊆ O.val) (hSP : S ⊆ P.val)
    (hxO : x∉O.val) (hxP : x∉P.val) :
    ∃ g : Mathieu24CodeModel,g • O=P ∧ (∀ i∈S,g.val i=i) ∧ g.val x=x := by
  classical
  obtain ⟨g,hfix,hg0⟩ := mathieu24_marked_octad_transitive S O.val P.val
    (by omega) O.prop P.prop hSO hSP
  have hg' : g • O=P := Subtype.ext hg0
  have hx' : g.val x∉P.val := by
    intro hm
    exact hxO ((mathieuOctad_transport_mem g O P hg' x).mp hm)
  obtain ⟨v,hv,_⟩ := mathieuOctadPointwise_regular P ⟨g.val x,hx'⟩ ⟨x,hxP⟩
  refine ⟨v.val.val*g,?_,?_,?_⟩
  · rw [mul_smul,hg']
    exact v.val.prop
  · intro i hiS
    change v.val.val.val (g.val i)=i
    rw [hfix i hiS]
    exact mathieuOctadPointwise_fixes_inside P v i (hSP hiS)
  · exact congrArg Subtype.val hv

end Atlas.Fischer
