import Atlas.Fischer.ParkerStandardKernel
import Atlas.Fischer.SignedOctads

namespace Atlas.Fischer
open Atlas.Codes

/-- The actual octads detect every cocode character, because the retained
Golay basis consists of twelve actual octad words. -/
theorem cocode_eq_zero_of_octad_pairing (d : Cocode)
    (h : ∀ O : Octad, cocodePairing (octadWord O) d=0) : d=0 := by
  apply cocodeDualEquiv.injective
  rw [map_zero]
  apply golayBasis.ext
  intro i
  let O : Octad := ⟨support (golayBasis i : BinaryWord),
    (octads_mem _).mpr ⟨golayBasis i,golay_octad_basis.2 i,rfl⟩⟩
  have hO : octadWord O=golayBasis i := by
    apply Subtype.ext
    apply support_injective
    exact octadWord_support O
  have he := h O
  rw [hO] at he
  exact he

/-- A standard automorphism inducing the identity and fixing every canonical
octad sign is the identity. The proof uses the full, actual cocode kernel. -/
theorem parkerStandard_eq_one_of_octad_signs (e : ParkerStandardGroup)
    (hπ : parkerStandardProjection e=1)
    (h : ∀ O : Octad, (e.val (canonicalOctadLift O).val).2=0) : e=1 := by
  obtain ⟨d,hd⟩ := parkerCocodeKernelHom_surjective ⟨e,hπ⟩
  have he : parkerCocodeHom d=e := congrArg Subtype.val hd
  have hd0 : d.toAdd=0 := by
    apply cocode_eq_zero_of_octad_pairing
    intro O
    have hh := h O
    rw [← he] at hh
    change 0+cocodePairing (octadWord O) d.toAdd=0 at hh
    simpa only [zero_add] using hh
  have hd1 : d=1 := Multiplicative.toAdd.injective hd0
  rw [← he,hd1,map_one]

end Atlas.Fischer
