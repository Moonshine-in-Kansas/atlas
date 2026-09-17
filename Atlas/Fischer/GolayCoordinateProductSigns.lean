import Atlas.Fischer.GolayCoordinateSigns

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Actual signed-octad multiplication gives a half-coordinate with a derived sign. -/
theorem product_signedOctads_global_eight (d f : SignedOctad) (c : golay)
    (hc : hammingNorm c.val=8) (hdf : d.val.1+f.val.1=c) :
    ∃ e : Bit, product (signedOctadVector d) (signedOctadVector f)=
      (parkerScalarSign e / 2) • golayCoordinateVector c (Or.inl hc) := by
  have hw := binary_weight_add d.val.1.val f.val.1.val
  rw [d.property,f.property] at hw
  change hammingNorm (d.val.1+f.val.1).val+2*overlap d.val.1.val f.val.1.val=8+8 at hw
  rw [hdf,hc,← signedOctadIntersection_overlap] at hw
  have hi : signedOctadIntersection d f=4 := by omega
  obtain ⟨e,he⟩ := signedOctadVector_global_eight (octadProductFour d f hi) c hc hdf
  refine ⟨e,?_⟩
  have hp := product_signedOctads_four d f hi
  rw [he] at hp
  linear_combination (norm := module) (1 / 2 : Scalar) • hp

/-- The disjoint branch retains the actual Omega multiplication sign in z_c. -/
theorem product_signedOctads_global_sixteen (d f : SignedOctad) (c : golay)
    (hc : hammingNorm c.val=16) (hdf : d.val.1+f.val.1=c) :
    ∃ e : Bit, product (signedOctadVector d) (signedOctadVector f)=
      (parkerScalarSign e / 2) • golayCoordinateVector c (Or.inr hc) := by
  have hw := binary_weight_add d.val.1.val f.val.1.val
  rw [d.property,f.property] at hw
  change hammingNorm (d.val.1+f.val.1).val+2*overlap d.val.1.val f.val.1.val=8+8 at hw
  rw [hdf,hc,← signedOctadIntersection_overlap] at hw
  have hi : signedOctadIntersection d f=0 := by omega
  have hl : (octadProductDisjoint d f hi).val.1=c+golayOne := congrArg (·+golayOne) hdf
  obtain ⟨e,he⟩ := theta_signedOctadVector_global_sixteen (octadProductDisjoint d f hi) c hc hl
  refine ⟨e,?_⟩
  have hp := product_signedOctads_disjoint d f hi
  rw [he] at hp
  linear_combination (norm := module) (1 / 2 : Scalar) • hp

/-- A complement-word term times a hyperplane term has the extra minus sign
forced by conjugate-linearity on theta. -/
theorem product_theta_signedOctad_global_sixteen (d f : SignedOctad) (c : golay)
    (hc : hammingNorm c.val=16) (hdf : d.val.1+f.val.1=c+golayOne) :
    ∃ e : Bit, product (theta • signedOctadVector d) (signedOctadVector f)=
      (parkerScalarSign e / 2) • golayCoordinateVector c (Or.inr hc) := by
  have h8 : hammingNorm (c+golayOne).val=8 := golayComplement_weight_sixteen c hc
  have hw := binary_weight_add d.val.1.val f.val.1.val
  rw [d.property,f.property] at hw
  change hammingNorm (d.val.1+f.val.1).val+2*overlap d.val.1.val f.val.1.val=8+8 at hw
  rw [hdf,h8,← signedOctadIntersection_overlap] at hw
  have hi : signedOctadIntersection d f=4 := by omega
  obtain ⟨e,he⟩ := theta_signedOctadVector_global_sixteen (octadProductFour d f hi) c hc hdf
  refine ⟨1+e,?_⟩
  have hp := product_signedOctads_four d f hi
  have hθ := congrArg (fun x : Coordinates => theta • x) hp
  rw [he] at hθ
  rw [product_smul_left,theta_conjugate,parkerScalarSign_one_add]
  linear_combination (norm := module) (-1 / 2 : Scalar) • hθ

end Atlas.Fischer
