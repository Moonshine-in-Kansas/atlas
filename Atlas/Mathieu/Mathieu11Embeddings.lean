import Atlas.Mathieu.Mathieu11PointStabilizer
import Atlas.Mathieu.Mathieu23PointStabilizer

noncomputable section
namespace Atlas.Codes

def mathieu11_to_m24 (D : Dodecad) (a : Mathieu12Points D) :
    Mathieu11PointModel D a →* Mathieu24CodeModel :=
  (mathieu12_embedding D).comp (mathieu11_embedding D a)

def mathieu11_to_m23 (D : Dodecad) (a : Mathieu12Points D) :
    Mathieu11PointModel D a →* Mathieu23PointModel a.val where
  toFun g := ⟨g.val.val,congrArg Subtype.val g.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mathieu11_to_m24_injective (D : Dodecad) (a : Mathieu12Points D) :
    Function.Injective (mathieu11_to_m24 D a) := Subtype.val_injective.comp Subtype.val_injective

theorem mathieu11_to_m23_injective (D : Dodecad) (a : Mathieu12Points D) :
    Function.Injective (mathieu11_to_m23 D a) := by
  intro g h he
  apply mathieu11_to_m24_injective D a
  exact congrArg (fun x : Mathieu23PointModel a.val => x.val) he

theorem mathieu11_embeddings_commute (D : Dodecad) (a : Mathieu12Points D) :
    (mathieu23_embedding a.val).comp (mathieu11_to_m23 D a) =
      (mathieu12_embedding D).comp (mathieu11_embedding D a) := rfl

theorem mathieu11_image_intersection (D : Dodecad) (a : Mathieu12Points D) :
    (mathieu11_to_m24 D a).range = Mathieu12DodecadModel D ⊓ Mathieu23PointModel a.val := by
  ext g
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨h.val.prop,congrArg Subtype.val h.prop⟩
  · rintro ⟨hD,ha⟩
    exact ⟨⟨⟨g,hD⟩,Subtype.ext ha⟩,rfl⟩

end Atlas.Codes
