import Atlas.Conway.Co3TriangleSevenTransport

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem co3_triangle_shape_iff_type (a : Omega) (t : Fin 8) (y : leech) :
    Co3TriangleShape a t y ↔
      (integerDot y.val y.val = 32 ∧ integerDot (normSixVector a-y).val (normSixVector a-y).val = 64) ∧
        co3TriangleCoordinateType a y.val = t := by
  constructor
  · intro h
    exact ⟨co3_triangle_shape_sound a t y h,co3_triangle_shape_coordinate_type a t y h⟩
  · rintro ⟨h,ht⟩
    obtain ⟨s,hs⟩ := co3_triangle_shape_exhaustive a ⟨y,h⟩
    have he : s = t := (co3_triangle_shape_coordinate_type a s y hs).symm.trans ht
    exact he ▸ hs

theorem co3TriangleCoordinateType_permutation (a : Omega) (g : Mathieu24CodeModel)
    (hg : g.val a = a) (y : IntegerCoordinates) :
    co3TriangleCoordinateType a (integerPermutation g.val y) = co3TriangleCoordinateType a y := by
  have hi : g.val.symm a = a := (g.val.symm_apply_eq).mpr hg.symm
  have hv : integerPermutation g.val y a = y a := by change y (g.val.symm a) = y a; rw [hi]
  have he (k : ℤ) : (∃ i, integerPermutation g.val y i = k) ↔ ∃ i, y i = k := by
    constructor
    · rintro ⟨i,hi⟩; exact ⟨g.val.symm i,hi⟩
    · rintro ⟨i,hi⟩
      refine ⟨g.val i,?_⟩
      change y (g.val.symm (g.val i)) = k
      simpa using hi
  simp only [co3TriangleCoordinateType,hv,he]

def co3TriangleType (a : Omega) (y : Co3Triangles a) : Fin 8 :=
  co3TriangleCoordinateType a y.val.val

theorem co3_triangle_type_preserved (a : Omega) (g : Mathieu23PointModel a) (y : Co3Triangles a) :
    co3TriangleType a (mathieu23ToNormSixStabilizer a g • y) = co3TriangleType a y :=
  co3TriangleCoordinateType_permutation a g.val g.prop y.val.val

theorem co3_triangle_mathieu_orbit_iff (a : Omega) (x y : Co3Triangles a) :
    (∃ g : Mathieu23PointModel a, mathieu23ToNormSixStabilizer a g • x = y) ↔
      co3TriangleType a x = co3TriangleType a y := by
  constructor
  · rintro ⟨g,rfl⟩
    exact (co3_triangle_type_preserved a g x).symm
  · intro ht
    have hx := (co3_triangle_shape_iff_type a (co3TriangleType a x) x.val).mpr ⟨x.prop,rfl⟩
    have hy := (co3_triangle_shape_iff_type a (co3TriangleType a x) y.val).mpr ⟨y.prop,ht.symm⟩
    obtain ⟨g,hg⟩ := co3_triangle_shape_transitive a _ x.val y.val hx hy
    exact ⟨g,Subtype.ext hg⟩

def co3TriangleTypeShapeEquiv (a : Omega) (t : Fin 8) :
    {y : Co3Triangles a // co3TriangleType a y = t} ≃ {y : leech // Co3TriangleShape a t y} where
  toFun y := ⟨y.val.val,(co3_triangle_shape_iff_type a t y.val.val).mpr ⟨y.val.prop,y.prop⟩⟩
  invFun y := ⟨⟨y.val,co3_triangle_shape_sound a t y.val y.prop⟩,
    co3_triangle_shape_coordinate_type a t y.val y.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem co3_triangle_type_card (a : Omega) (t : Fin 8) :
    Nat.card {y : Co3Triangles a // co3TriangleType a y = t} = co3TriangleSize t := by
  rw [Nat.card_congr (co3TriangleTypeShapeEquiv a t),co3_triangle_shape_card]

end Atlas.Conway
