import Atlas.Sporadic.McLaughlinSimplicity
import Atlas.Conway.LeechPlaneComplement
import Atlas.Sporadic.Conway2

noncomputable section
namespace Atlas.Sporadic.McLaughlin
open Atlas.Codes Atlas.Lattices Atlas.Conway

abbrev Complement := leechPlaneComplement vector endpoint

theorem plane_gram_determinant : leechPlaneGramDet vector endpoint = 960 := by
  unfold leechPlaneGramDet
  rw [triangle_gram.1,triangle_gram.2.1,triangle_gram.2.2]
  norm_num

theorem complement_rank : Module.finrank ℤ Complement = 22 :=
  leechPlaneComplement_rank vector endpoint (by rw [triangle_gram.1]; decide)
    (by rw [plane_gram_determinant]; decide)

theorem complement_free : Module.Free ℤ Complement := inferInstance

theorem complement_finite : Module.Finite ℤ Complement := inferInstance

def integralRepresentation : Model →* (Complement ≃ₗ[ℤ] Complement) :=
  leechPlaneRepresentation vector endpoint

theorem integralRepresentation_injective : Function.Injective integralRepresentation :=
  leechPlaneRepresentation_injective vector endpoint (by rw [plane_gram_determinant]; decide)

theorem integralRepresentation_preserves (g : Model) (z t : Complement) :
    integerDot (integralRepresentation g z).val.val (integralRepresentation g t).val.val =
      integerDot z.val.val t.val.val := leechPlaneRepresentation_preserves vector endpoint g z t

/-- The retained normalization already uses the public Co2 base vector. -/
theorem endpoint_eq_conway2_vector : endpoint = Conway2.vector.val := rfl

/-- An explicit norm-four transporter: identity in the common coordinate marking. -/
def normFourTransporter : LeechIsometryGroup := 1

theorem normFourTransporter_spec : normFourTransporter.val endpoint = Conway2.vector.val := rfl

def toConway2 : Model →* Conway2.Model where
  toFun g := ⟨g.val.val,g.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toConway2_injective : Function.Injective toConway2 := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun k : Conway2.Model => (k : LeechIsometryGroup)) he

theorem toConway2_compatible (g : Model) : Conway2.embedding (toConway2 g) = embedding g := rfl

theorem toConway3_compatible (g : Model) : Conway3.embedding (toConway3 g) = embedding g := rfl

theorem toConway1_via_conway2 (g : Model) : Conway2.toConway1 (toConway2 g) = toConway1 g := rfl

theorem toConway1_via_conway3 (g : Model) : Conway3.toConway1 (toConway3 g) = toConway1 g := rfl

theorem triangleMathieuEquiv_compatible (g : McLMathieuModel) :
    (triangleMathieuEquiv g).val = mathieu22Embedding g := rfl

theorem mathieu22Embedding_range : mathieu22Embedding.range = TriangleStabilizer := by
  ext g
  constructor
  · rintro ⟨p,rfl⟩
    exact (triangleMathieuEquiv p).prop
  · intro hg
    obtain ⟨p,hp⟩ := triangleMathieuEquiv.surjective ⟨g,hg⟩
    exact ⟨p,congrArg Subtype.val hp⟩

end Atlas.Sporadic.McLaughlin
