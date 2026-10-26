import Atlas.Tits.TransferWitnessCycles
import Atlas.Rudvalis.FrameSignConjugation

/-! Actual point-fixing row translations centralize E₃ and move any point of
an external coordinate row to any other point of that row. -/

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.Codes.Quaternary

/-- The inherited row kernel centralizes every pure row sign. -/
theorem rowKernel_commute_rowSign (g : codeRowKernel) (a : E) :
    Commute g.val (seedARowSign a) := by
  have hlin : codeBlockLinearHom g.val⁻¹ = 1 := by
    rw [map_inv,show codeBlockLinearHom g.val = 1 from g.prop,inv_one]
  have hrow : codeRowImage g.val⁻¹ = Equiv.refl Point := by
    rw [codeRowImage_eq_linearPoint,hlin]
    rfl
  have hconj : g.val * seedARowSign a * g.val⁻¹ = seedARowSign a := by
    apply Subtype.ext
    change g.val.val * rowSignHom (Multiplicative.ofAdd (fun p => dot a p.val)) *
      g.val.val⁻¹ = rowSignHom (Multiplicative.ofAdd (fun p => dot a p.val))
    rw [rowSignHom_conjugate,hrow]
    rfl
  exact (mul_inv_eq_iff_eq_mul).mp hconj

/-- A point-fixing translation moving between any two coordinates of another
row exists in the actual code group, and centralizes the actual E₃. -/
theorem point_row_translation_centralizer (p : Point) (hp : p ≠ rowLabel 0) (x y : E) :
    ∃ g : codeReferenceStabilizer,
      Commute g pointE3 ∧
      g.val • coordinateCross (p,x) = coordinateCross (p,y) := by
  obtain ⟨B,hB0,hBp⟩ := matrixAt_two_points (rowLabel 0) p hp.symm 0 (x+y)
  obtain ⟨g,hg⟩ := codeRowKernel_translation_lift B
  have hfix : g.val ∈ codeReferenceStabilizer := by
    change g.val • localReferenceCross = localReferenceCross
    rw [localReferenceCross_eq,coordinateCross_action,hg]
    change coordinateCross (rowLabel 0,0+matrixAt B (rowLabel 0).val) =
      coordinateCross (rowLabel 0,0)
    rw [hB0,add_zero]
  let u : codeReferenceStabilizer := ⟨g.val,hfix⟩
  refine ⟨u,?_,?_⟩
  · exact Subtype.ext (rowKernel_commute_rowSign g (binaryLabel 3)).eq
  · change g.val • coordinateCross (p,x) = coordinateCross (p,y)
    rw [coordinateCross_action,hg]
    change coordinateCross (p,x+matrixAt B p.val) = coordinateCross (p,y)
    rw [hBp,← add_assoc,vector_add_self,zero_add]

/-- The centralizer of alpha² in the actual ambient stabilizer is transitive
on the four coordinate neighbours in each of the other six rows. -/
theorem alphaSquare_centralizer_row_transitive (p : Point) (hp : p ≠ rowLabel 0)
    (a b : Neighbours) (ha : a.val ∈ coordinateRowFrame p)
    (hb : b.val ∈ coordinateRowFrame p) :
    ∃ g : Ambient, Commute g (localAlpha^2) ∧ g • a = b := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  obtain ⟨g,hg,hxy⟩ := point_row_translation_centralizer p hp x y
  refine ⟨codePointHom g,?_,?_⟩
  · rw [localAlpha_square]
    exact hg.map codePointHom
  · apply Subtype.ext
    change g.val • a.val = b.val
    rw [← hx,← hy]
    exact hxy

end Atlas.Tits
