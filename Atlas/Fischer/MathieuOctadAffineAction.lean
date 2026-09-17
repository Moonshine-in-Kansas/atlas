import Atlas.Fischer.MathieuOctadExteriorFaithful
import Atlas.Fischer.OctadAffineCode
import Atlas.Fischer.ParkerCodeAction
import Atlas.LinearAlgebra.AffinePermutation

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

abbrev BinaryFourSpace := Fin 4 → Bit

def mathieuOctadCoordinatePerm (O : Octad) (g : MathieuOctadStabilizer O) :
    Equiv.Perm BinaryFourSpace :=
  (octadExteriorCoordinates O).symm.trans
    ((mathieuOctadExteriorPerm O g).trans (octadExteriorCoordinates O))

theorem mathieuOctadCoordinatePerm_coordinates (O : Octad) (g : MathieuOctadStabilizer O)
    (v : BinaryFourSpace) :
    ((octadExteriorCoordinates O).symm (mathieuOctadCoordinatePerm O g v)).val =
      g.val.val ((octadExteriorCoordinates O).symm v).val := by
  simp [mathieuOctadCoordinatePerm, mathieuOctadExteriorPerm]

/-- Pullback along the actual stabilizer permutation remains in the actual code. -/
def mathieuOctadPullbackWord (O : Octad) (g : MathieuOctadStabilizer O)
    (c : octadShortenedCode O) : octadShortenedCode O :=
  ⟨parkerCodeEquiv g.val⁻¹ c.val, by
    rw [mem_octadShortenedCode]
    intro i hi
    change c.val.val (g.val.val i) = 0
    exact (mem_octadShortenedCode O c.val).mp c.prop _
      ((mathieuOctadStabilizer_mem_iff O g i).mpr hi)⟩

theorem mathieuOctadPullbackWord_apply (O : Octad) (g : MathieuOctadStabilizer O)
    (c : octadShortenedCode O) (v : BinaryFourSpace) :
    octadAffineWord O (mathieuOctadPullbackWord O g c) v =
      octadAffineWord O c (mathieuOctadCoordinatePerm O g v) := by
  change c.val.val (g.val.val ((octadExteriorCoordinates O).symm v).val) =
    c.val.val ((octadExteriorCoordinates O).symm (mathieuOctadCoordinatePerm O g v)).val
  rw [mathieuOctadCoordinatePerm_coordinates]

theorem mathieuOctadCoordinatePerm_affine (O : Octad) (g : MathieuOctadStabilizer O) :
    ∀ i, ∃ a : Bit, ∃ l : BinaryFourSpace →ₗ[Bit] Bit,
      ∀ v, mathieuOctadCoordinatePerm O g v i = a+l v := by
  intro i
  have hi : (fun v : BinaryFourSpace => v i) ∈ binaryAffineCodeFour :=
    ⟨0,LinearMap.proj i,fun _ => (zero_add _).symm⟩
  rw [← octadAffineWord_range O] at hi
  obtain ⟨c,hc⟩ := hi
  obtain ⟨a,l,hl⟩ := octadAffineWord_mem O (mathieuOctadPullbackWord O g c)
  refine ⟨a,l,?_⟩
  intro v
  rw [← hl v,mathieuOctadPullbackWord_apply, hc]

def mathieuOctadAffineEquiv (O : Octad) (g : MathieuOctadStabilizer O) :
    BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace :=
  Atlas.LinearAlgebra.affineEquivOfCoordinateAffine (mathieuOctadCoordinatePerm O g)
    (mathieuOctadCoordinatePerm_affine O g)

def mathieuOctadAffineHom (O : Octad) :
    MathieuOctadStabilizer O →* (BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace) where
  toFun := mathieuOctadAffineEquiv O
  map_one' := by
    apply AffineEquiv.ext
    intro v
    change mathieuOctadCoordinatePerm O 1 v = v
    simp [mathieuOctadCoordinatePerm,mathieuOctadExteriorPerm]
  map_mul' g h := by
    apply AffineEquiv.ext
    intro v
    change mathieuOctadCoordinatePerm O (g*h) v =
      mathieuOctadCoordinatePerm O g (mathieuOctadCoordinatePerm O h v)
    simp [mathieuOctadCoordinatePerm,mathieuOctadExteriorPerm]

theorem mathieuOctadAffineHom_injective (O : Octad) :
    Function.Injective (mathieuOctadAffineHom O) := by
  intro g h he
  apply mathieuOctadExteriorHom_injective O
  apply Equiv.ext
  intro i
  change mathieuOctadExteriorPerm O g i = mathieuOctadExteriorPerm O h i
  have hh := congrArg (fun A : BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace =>
    A (octadExteriorCoordinates O i)) he
  simpa [mathieuOctadAffineHom,mathieuOctadAffineEquiv,mathieuOctadCoordinatePerm] using hh

end Atlas.Fischer
