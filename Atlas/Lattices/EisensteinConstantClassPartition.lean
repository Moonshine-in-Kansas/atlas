import Atlas.Lattices.EisensteinFrames
import Atlas.Lattices.EisensteinNormalizedShortCodes
import Atlas.Codes.TernaryConstantHexadPairs

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- The complementary constant-hexad partition is intrinsic to a short frame. -/
theorem eisenstein_constant_frame_partition (s t : Finset (Fin 12))
    (x y : EisensteinShell 6) (u v : EisensteinCoordinates)
    (hu : x.val.val=eisensteinTheta • u) (hv : y.val.val=eisensteinTheta • v)
    (hs : eisensteinWordResidue u=ternaryTriadWord s)
    (ht : eisensteinWordResidue v=ternaryTriadWord t)
    (he : eisensteinFramePair (eisensteinClass x.val)=
      eisensteinFramePair (eisensteinClass y.val)) :
    ternaryConstantHexadPair s=ternaryConstantHexadPair t := by
  have hsupport (a : Finset (Fin 12)) : ternarySupport (ternaryTriadWord a)=a := by
    ext i; simp [ternarySupport,ternaryTriadWord]
  rw [eisensteinFramePair_eq_iff] at he
  rcases he with he|he
  · rcases eisenstein_constant_hexad_class_normalized s x y u v hu hv hs he with h|h
    · rw [ht] at h
      have hh := congrArg ternarySupport h
      simp only [hsupport] at hh
      rw [hh]
    · rw [ht] at h
      have hh := congrArg ternarySupport h
      simp only [ternarySupport_neg,hsupport] at hh
      rw [hh,ternaryConstantHexadPair_compl]
  · let z : EisensteinShell 6 := ⟨-y.val,(eisensteinNorm_neg y.val).trans y.property⟩
    have hz : z.val.val=eisensteinTheta • (-v) := by
      change -y.val.val=eisensteinTheta • (-v)
      rw [hv,smul_neg]
    have hc : eisensteinClass x.val=eisensteinClass z.val := by
      change eisensteinClass x.val=eisensteinClass (-y.val)
      rw [map_neg]; exact he
    have hr : eisensteinWordResidue (-v)= -ternaryTriadWord t := by
      rw [← ht]
      funext i
      simp [eisensteinWordResidue]
    rcases eisenstein_constant_hexad_class_normalized s x z u (-v) hu hz hs hc with h|h
    · rw [hr] at h
      have hh := congrArg ternarySupport h
      simp only [ternarySupport_neg,hsupport] at hh
      rw [hh]
    · rw [hr] at h
      have hh := congrArg ternarySupport h
      simp only [ternarySupport_neg,hsupport] at hh
      rw [hh,ternaryConstantHexadPair_compl]

end Atlas.Lattices
