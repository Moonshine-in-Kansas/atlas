import Atlas.Fischer.MathieuOctadTranslations
import Atlas.Families.Alternating.Stabilizers

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Membership transport uses the actual coordinate permutation, not an abstract
identification of equally sized octad orbits. -/
theorem mathieuOctad_transport_mem (g : Mathieu24CodeModel) (O P : Octad)
    (hg : g • O=P) (i : Omega) : g.val i∈P.val ↔ i∈O.val := by
  classical
  have hv := congrArg Subtype.val hg
  change O.val.image g.val=P.val at hv
  rw [← hv,Finset.mem_image]
  exact ⟨fun ⟨j,hj,h⟩ => g.val.injective h ▸ hj,fun hi => ⟨i,hi,rfl⟩⟩

theorem mathieuOctadPointwise_fixes_inside (O : Octad) (g : mathieuOctadPointwise O)
    (i : Omega) (hi : i∈O.val) : g.val.val.val i=i := by
  have h := congrArg (fun a : alternatingGroup (OctadInterior O) => a.val ⟨i,hi⟩) g.prop
  exact congrArg Subtype.val h

end Atlas.Fischer
