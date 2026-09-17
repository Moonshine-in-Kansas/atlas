import Atlas.Fischer.BinaryFourAffineEven
import Atlas.Mathieu.Mathieu24Alternating

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

abbrev OctadInterior (O : Octad) := {i : Omega // i ∈ O.val}

def mathieuOctadInteriorPerm (O : Octad) (g : MathieuOctadStabilizer O) :
    Equiv.Perm (OctadInterior O) :=
  g.val.val.subtypePerm (mathieuOctadStabilizer_mem_iff O g)

def mathieuOctadInteriorHom (O : Octad) :
    MathieuOctadStabilizer O →* Equiv.Perm (OctadInterior O) where
  toFun := mathieuOctadInteriorPerm O
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mathieuOctadExterior_even (O : Octad) (g : MathieuOctadStabilizer O) :
    Equiv.Perm.sign (mathieuOctadExteriorPerm O g) = 1 := by
  have h := binaryFourAffine_even (mathieuOctadAffineEquiv O g)
  have hp : (mathieuOctadAffineEquiv O g).toEquiv =
      (octadExteriorCoordinates O).permCongr (mathieuOctadExteriorPerm O g) := by
    apply Equiv.ext
    intro v
    rfl
  rw [hp] at h
  rwa [Equiv.Perm.sign_permCongr] at h

theorem mathieuOctadInterior_even (O : Octad) (g : MathieuOctadStabilizer O) :
    Equiv.Perm.sign (mathieuOctadInteriorPerm O g) = 1 := by
  classical
  have he : (mathieuOctadInteriorPerm O g).subtypeCongr (mathieuOctadExteriorPerm O g) = g.val.val := by
    apply Equiv.ext
    intro i
    by_cases hi : i ∈ O.val <;>
      simp [Equiv.Perm.subtypeCongr, mathieuOctadInteriorPerm, mathieuOctadExteriorPerm, hi]
  have h := Equiv.Perm.sign_subtypeCongr
    (mathieuOctadInteriorPerm O g) (mathieuOctadExteriorPerm O g)
  rw [he,mathieu24_even g.val,mathieuOctadExterior_even,mul_one] at h
  convert! h.symm using 1
  exact congrArg (fun inst : Fintype (OctadInterior O) =>
    @Equiv.Perm.sign (OctadInterior O) inferInstance inst (mathieuOctadInteriorPerm O g))
    (Subsingleton.elim _ _)

/-- The actual restriction into the alternating group on the eight marked octad points. -/
def mathieuOctadAlternatingHom (O : Octad) : MathieuOctadStabilizer O →* alternatingGroup (OctadInterior O) :=
  (mathieuOctadInteriorHom O).codRestrict _ (fun g =>
    (Equiv.Perm.mem_alternatingGroup).mpr (mathieuOctadInterior_even O g))

end Atlas.Fischer
