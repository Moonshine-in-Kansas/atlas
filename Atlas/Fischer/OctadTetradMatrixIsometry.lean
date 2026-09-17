import Atlas.Fischer.FourPairHermitianRows
import Atlas.Fischer.OctadTetradPairedBasis
import Atlas.Fischer.OctadTetradComplementRows

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadTetradPairedFamily_orthonormal {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (p q : OctadTetradFibre O T × Fin 2) :
    hermitian (octadTetradPairedFamily Q T hT D d hd p) (octadTetradPairedFamily Q T hT D d hd q) =
      if p = q then 1 else 0 := by
  rw [octadTetradPairedFamily_eq, octadTetradPairedFamily_eq]
  by_cases hpq : p = q
  · subst q
    rw [ite_eq_left rfl]
    exact signedOctadVector_norm _
  · have hn := (octadTetradPairedLabel_support_injective Q T hTO hT D d hd).ne hpq
    simp only [signedOctadVector, hermitian_smul_left, hermitian_smul_right,
      hermitian_xOctad, ite_eq_right hn, ite_eq_right hpq, mul_zero]

/-- Both halves of the actual reflection are the verified theta-coupled J-2I rows. -/
theorem rootMap_octadic_tetrad_row {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (p : OctadTetradFibre O T × Fin 2) :
    rootMap (octadicRoot Q 0) (octadTetradPairedFamily Q T hT D d hd p) =
      fourPairThetaRow (octadTetradPairedFamily Q T hT D d hd) p.1 p.2 := by
  rcases p with ⟨E,a⟩
  fin_cases a
  · simpa [octadTetradPairedFamily, fourPairThetaRow, fourPairDifference, Fin.ext_iff] using
      rootMap_octadic_tetrad_first_row Q T hT D d hd E
  · simpa [octadTetradPairedFamily, fourPairThetaRow, fourPairDifference, Fin.ext_iff] using
      rootMap_octadic_tetrad_second_row Q T hTO hT D d hd E

theorem
 rootMap_octadic_tetrad_pairing {O : Octad} (Q : OctadCalibration O)
    (T : Finset Omega) (hTO : T ⊆ O.val) (hT : T.card = 4) (D : OctadTetradFibre O T)
    (d : ParkerLoop) (hd : d.1 = octadWord D.val) (p q : OctadTetradFibre O T × Fin 2) :
    hermitian (rootMap (octadicRoot Q 0) (octadTetradPairedFamily Q T hT D d hd p))
      (rootMap (octadicRoot Q 0) (octadTetradPairedFamily Q T hT D d hd q)) =
      if p = q then 1 else 0 := by
  rw [rootMap_octadic_tetrad_row Q T hTO hT, rootMap_octadic_tetrad_row Q T hTO hT]
  have hc : Fintype.card (OctadTetradFibre O T) = 4 :=
    Nat.card_eq_fintype_card.symm.trans (octadTetradFibre_card O T hTO hT)
  have hh := fourPairThetaRow_orthonormal hc (octadTetradPairedFamily Q T hT D d hd)
    (fun p q => by
      by_cases h : p = q <;> simpa only [h, ite_true, ite_false] using
        octadTetradPairedFamily_orthonormal Q T hTO hT D d hd p q) p.1 q.1 p.2 q.2
  by_cases h : p = q <;> simpa only [Prod.eta, h, ite_true, ite_false] using hh

end Atlas.Fischer
