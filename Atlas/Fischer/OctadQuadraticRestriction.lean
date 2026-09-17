import Atlas.Algebra.BinaryAffineFunctions
import Atlas.Fischer.OctadAffineCode

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
open scoped BigOperators

/-- The full affine-function description and the generic affine monomial code
are the same literal submodule of functions on sixteen binary coordinates. -/
theorem binaryAffineCodeFour_eq : binaryAffineCodeFour = binaryAffineCode := by
  ext w
  exact (binaryAffineCode_mem_iff w).symm

/-- Puncturing the retained Golay code using the already verified exterior
coordinate labelling of the actual octad. -/
noncomputable def octadExteriorWord (O : Octad) : golay →ₗ[Bit] BinaryFourWord where
  toFun c v := c.val ((octadExteriorCoordinates O).symm v).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem octadExteriorWord_shortened (O : Octad) (c : octadShortenedCode O) :
    octadExteriorWord O c.val = octadAffineWord O c := rfl

/-- The punctured/shortened pairing is exactly the full Golay pairing, since
the shortened word vanishes on the removed octad. -/
theorem octadExteriorWord_shortened_dot (O : Octad) (c : golay) (b : octadShortenedCode O) :
    binaryDot (octadExteriorWord O c) (octadAffineWord O b) = binaryDot c.val b.val.val := by
  classical
  change (∑ v, c.val ((octadExteriorCoordinates O).symm v).val *
    b.val.val ((octadExteriorCoordinates O).symm v).val) = ∑ i, c.val i*b.val.val i
  rw [Equiv.sum_comp (octadExteriorCoordinates O).symm
    (fun i : OctadExterior O => c.val i.val*b.val.val i.val)]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Omega => i ∈ O.val)
    (fun i => c.val i*b.val.val i)
  have hzfun : (fun i : {i : Omega // i ∈ O.val} => c.val i.val*b.val.val i.val) = 0 := by
    funext i
    rw [(mem_octadShortenedCode O b.val).mp b.property i.val i.property,mul_zero]
    rfl
  simpa only [hzfun,Pi.zero_apply,Finset.sum_const_zero,zero_add] using h

/-- Self-duality of the retained Golay code forces each actual punctured word
into the literal quadratic evaluation code. -/
theorem octadExteriorWord_mem_quadratic (O : Octad) (c : golay) :
    octadExteriorWord O c ∈ binaryQuadraticCode := by
  rw [binaryQuadraticCode_eq_affine_orthogonal]
  intro w hw
  rw [← binaryAffineCodeFour_eq,← octadAffineWord_range O] at hw
  obtain ⟨b,rfl⟩ := hw
  rw [binaryDot_symmetric,octadExteriorWord_shortened_dot]
  exact golay_selfOrthogonal b.val.property c.val c.property

end Atlas.Fischer
