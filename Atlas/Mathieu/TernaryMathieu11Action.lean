import Atlas.Mathieu.TernaryConstantAction
import Atlas.Mathieu.DodecadComplement
import Atlas.Mathieu.Mathieu11Simplicity

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
namespace Atlas.Codes

def ternaryComplementPoint : Mathieu12Points (dodecadComplement ternaryComparisonDodecad) :=
  ⟨ternaryConstantPoint, by
    change ternaryConstantPoint ∈ ternaryBinaryDodecadSetᶜ
    decide⟩

/-- The existing binary-Golay M11, acting exceptionally on the opposite dodecad. -/
abbrev TernaryMathieu11 := Mathieu11PointModel
  (dodecadComplement ternaryComparisonDodecad) ternaryComplementPoint

def ternaryMathieu11ToDodecad : TernaryMathieu11 →*
    Mathieu12DodecadModel ternaryComparisonDodecad :=
  (MulEquiv.subgroupCongr (mathieu12_complement_stabilizer ternaryComparisonDodecad)).toMonoidHom.comp
    (mathieu11_embedding _ _)

def ternaryMathieu11Hom : TernaryMathieu11 →* Equiv.Perm (Fin 12) :=
  ternaryWittMathieuHom.comp ternaryMathieu11ToDodecad

theorem ternaryMathieu11Hom_injective : Function.Injective ternaryMathieu11Hom := by
  exact ternaryWittMathieuHom_injective.comp
    ((MulEquiv.subgroupCongr (mathieu12_complement_stabilizer ternaryComparisonDodecad)).injective.comp
      (mathieu11_embedding_injective _ _))

theorem ternaryMathieu11_fixes_constant (g : TernaryMathieu11) :
    (ternaryMathieu11ToDodecad g).val.val ternaryConstantPoint = ternaryConstantPoint :=
  congrArg Subtype.val g.prop

theorem ternaryMathieu11_preserves (g : TernaryMathieu11)
    (w : TernaryWord) (hw : w ∈ ternaryGolay) :
    ternaryCoordinateMap (ternaryMathieu11Hom g) w ∈ ternaryGolay :=
  ternaryWitt_fix_constant_preserves_code (ternaryMathieu11ToDodecad g)
    (ternaryMathieu11_fixes_constant g) w hw

theorem ternaryMathieu11_order : Nat.card TernaryMathieu11 = 7920 :=
  mathieu11_order _ _

theorem ternaryMathieu11_simple : IsSimpleGroup TernaryMathieu11 :=
  mathieu11_simple _ _

end Atlas.Codes
