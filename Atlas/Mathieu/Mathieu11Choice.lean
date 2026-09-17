import Atlas.Mathieu.Mathieu11Embeddings
import Atlas.Mathieu.Mathieu12Choice

noncomputable section
namespace Atlas.Codes

def mathieu11FlagEquiv (D : Dodecad) (a : Mathieu12Points D) :
    Mathieu11PointModel D a ≃* MulAction.stabilizer Mathieu24CodeModel (D,a.val) where
  toFun g := ⟨g.val.val,Prod.ext g.val.prop (congrArg Subtype.val g.prop)⟩
  invFun g := ⟨⟨g.val,congrArg Prod.fst g.prop⟩,Subtype.ext (congrArg Prod.snd g.prop)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def mathieu11ChoiceEquiv {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val) :
    Mathieu11PointModel D a ≃* Mathieu11PointModel E b :=
  (mathieu11FlagEquiv D a).trans ((MulAction.stabilizerEquivStabilizer
    (show (E,b.val) = g • (D,a.val) from (Prod.ext hg ha).symm)).trans
      (mathieu11FlagEquiv E b).symm)

theorem mathieu11Choice_embedding {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val)
    (h : Mathieu11PointModel D a) :
    mathieu11_to_m24 E b (mathieu11ChoiceEquiv hg ha h) = g * mathieu11_to_m24 D a h * g⁻¹ := rfl

def mathieu11ChoicePoints {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val) :
    Mathieu11Points D a ≃ Mathieu11Points E b :=
  (mathieu12ChoicePoints hg).subtypeEquiv (fun x => by
    change (x ≠ a) ↔ (mathieu12ChoicePoints hg x ≠ b)
    have hab : mathieu12ChoicePoints hg a = b := Subtype.ext ha
    rw [← hab]
    exact (mathieu12ChoicePoints hg).injective.ne_iff.symm)

theorem mathieu11ChoicePoints_coordinate {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val)
    (x : Mathieu11Points D a) : (mathieu11ChoicePoints hg ha x).val.val = g.val x.val.val := rfl

theorem mathieu11Choice_equivariant {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val)
    (h : Mathieu11PointModel D a) (x : Mathieu11Points D a) :
    mathieu11ChoicePoints hg ha (h • x) = mathieu11ChoiceEquiv hg ha h • mathieu11ChoicePoints hg ha x := by
  apply Subtype.ext
  apply Subtype.ext
  change g.val ((mathieu11_to_m24 D a h).val x.val.val) =
    (mathieu11_to_m24 E b (mathieu11ChoiceEquiv hg ha h)).val (g.val x.val.val)
  rw [mathieu11Choice_embedding]
  change g.val ((mathieu11_to_m24 D a h).val x.val.val) =
    g.val ((mathieu11_to_m24 D a h).val (g.val⁻¹ (g.val x.val.val)))
  rw [Equiv.Perm.inv_def,Equiv.symm_apply_apply]

end Atlas.Codes
