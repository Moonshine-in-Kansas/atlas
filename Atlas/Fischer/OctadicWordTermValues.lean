import Atlas.Fischer.OctadicWordEigenvectors
import Atlas.Fischer.DuadComponentWeights
import Atlas.Fischer.OctadicCrossingAxis

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra
attribute [local instance] Classical.propDecidable

theorem octadicWordTerm_zero {O : Octad} (Q : OctadCalibration O) :
    octadicWordTerm Q 0=octadicAxisPart O :=
  octadicWordTerm_index Q (.inl ())

theorem octadicWordTerm_one {O : Octad} (Q : OctadCalibration O) :
    octadicWordTerm Q (octadShortenedOne O)=theta • signedOctadVector Q.octadLift :=
  octadicWordTerm_index Q (.inr (.inl ()))

theorem octadicWordTerm_hyperplane {O : Octad} (Q : OctadCalibration O)
    (b : OctadShortenedHyperplane O) : octadicWordTerm Q b.val=calibratedHyperplaneVector Q b :=
  octadicWordTerm_index Q (.inr (.inr b))

theorem duadPair_disjoint_octad_intersections (F G D : Octad)
    (hFG : (F.val ∩ G.val).card=2) (hGD : Disjoint G.val D.val) :
    (F.val ∩ D.val).card=2 ∨ (F.val ∩ D.val).card=4 := by
  have h0 : (F.val ∩ D.val).card ≠ 0 := by
    intro h
    have hF : Disjoint F.val D.val := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h)
    exact octad_not_disjoint_duad_pair F G D hFG (Finset.disjoint_union_right.mpr ⟨hF.symm,hGD.symm⟩)
  have h8 : (F.val ∩ D.val).card ≠ 8 := by
    intro h
    have hi : F.val ∩ D.val=F.val := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [h,octad_size F.val F.property])
    have hf : F.val ⊆ D.val := hi ▸ Finset.inter_subset_right
    have he : F.val=D.val := Finset.eq_of_subset_of_card_le hf
      (by rw [octad_size F.val F.property,octad_size D.val D.property])
    have hz : F.val ∩ G.val=∅ := Finset.disjoint_iff_inter_eq_empty.mp (he ▸ hGD.symm)
    rw [hz] at hFG
    simp at hFG
  rcases octad_intersection_sizes F.val D.val F.property D.property with h | h | h | h
  · exact (h0 h).elim
  · exact Or.inl h
  · exact Or.inr h
  · exact (h8 h).elim

theorem rationalCoordinateEquiv_scalar_rat_smul (a : ℚ) (x : Coordinates) (p : RationalCoordinateIndex) :
    rationalCoordinateEquiv ((a : Scalar) • x) p=a*rationalCoordinateEquiv x p := by
  rw [Rat.cast_smul_eq_qsmul,map_smul]
  rfl

theorem rationalCoordinate_signedOctad (d : SignedOctad) :
    rationalCoordinateEquiv (signedOctadVector d) (.inr (signedOctadSupport d),0)=
      rationalBitSign d.val.2 := by
  rw [rationalCoordinateEquiv_real]
  by_cases hd : d.val.2=0 <;>
    norm_num [show (1 : Scalar).re=1 from rfl,show (1 : Scalar).im=0 from rfl,signedOctadVector,Pi.smul_apply,xOctad_octad_apply,parkerScalarSign,rationalBitSign,hd]

theorem rationalCoordinate_theta_signedOctad (d : SignedOctad) :
    rationalCoordinateEquiv (theta • signedOctadVector d) (.inr (signedOctadSupport d),1)=
      rationalBitSign d.val.2 := by
  rw [rationalCoordinateEquiv_theta]
  by_cases hd : d.val.2=0 <;>
    norm_num [signedOctadVector,Pi.smul_apply,xOctad_octad_apply,parkerScalarSign,rationalBitSign,hd,
      theta,omega,rationalOmega,QuadraticAlgebra.omega]

end Atlas.Fischer
