import Atlas.Fischer.QuinticCocodeCovariance
import Atlas.Fischer.RationalCoordinateSpace

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem scalar_rational_of_star_fixed (z : Scalar) (hz : star z=z) :
    ∃ q : ℚ, z=q • (1 : Scalar) := by
  have h := congrArg (fun w : Scalar => (scalarRealThetaEquiv w).2) hz
  rw [scalarRealThetaEquiv_star] at h
  have h0 : (scalarRealThetaEquiv z).2=0 := by dsimp at h; linarith
  refine ⟨(scalarRealThetaEquiv z).1,?_⟩
  have hd := scalarRealThetaEquiv_decomposition z
  simpa only [h0,zero_smul,add_zero] using hd

theorem scalar_theta_rational_of_star_neg (z : Scalar) (hz : star z= -z) :
    ∃ q : ℚ, z=q • theta := by
  have h := congrArg (fun w : Scalar => (scalarRealThetaEquiv w).1) hz
  rw [scalarRealThetaEquiv_star,map_neg] at h
  have h0 : (scalarRealThetaEquiv z).1=0 := by dsimp at h; linarith
  refine ⟨(scalarRealThetaEquiv z).2,?_⟩
  have hd := scalarRealThetaEquiv_decomposition z
  simpa only [h0,zero_smul,zero_add] using hd

/-- Odd cocode covariance determines the exact rational/ theta-rational phase in E. -/
theorem scalar_phases_of_cocode_covariance (w : golay) (z : Scalar)
    (h : ∀ d : Cocode, scalarParityAut (cocodeParity d) z=cocodeScalarCharacter d w*z) :
    (w=0 → ∃ q : ℚ, z=q • (1 : Scalar)) ∧
    (w=golayOne → ∃ q : ℚ, z=q • theta) := by
  obtain ⟨d,hd⟩ := cocodeParity_surjective 1
  have he := h d
  rw [hd,scalarParityAut_one] at he
  constructor
  · intro hw
    apply scalar_rational_of_star_fixed
    simpa [hw,cocodeScalarCharacter,cocodePairing,parkerScalarSign] using he
  · intro hw
    apply scalar_theta_rational_of_star_neg
    have hp : cocodePairing golayOne d=1 := hd
    simpa [hw,cocodeScalarCharacter,hp,parkerScalarSign] using he

theorem coordinateCubic_rational_phase (i j k : CoordinateIndex)
    (h : coordinateTripleWord i j k=0) : ∃ q : ℚ, coordinateCubic i j k=q • (1 : Scalar) :=
  (scalar_phases_of_cocode_covariance _ _ (fun d => (coordinateCubic_cocode d i j k).symm)).1 h

theorem coordinateCubic_theta_phase (i j k : CoordinateIndex)
    (h : coordinateTripleWord i j k=golayOne) : ∃ q : ℚ, coordinateCubic i j k=q • theta :=
  (scalar_phases_of_cocode_covariance _ _ (fun d => (coordinateCubic_cocode d i j k).symm)).2 h

theorem coordinateQuintic_rational_phase (i j k : CoordinateIndex)
    (h : coordinateTripleWord i j k=0) : ∃ q : ℚ, coordinateQuintic i j k=q • (1 : Scalar) :=
  (scalar_phases_of_cocode_covariance _ _ (fun d => coordinateQuintic_cocode d i j k)).1 h

theorem coordinateQuintic_theta_phase (i j k : CoordinateIndex)
    (h : coordinateTripleWord i j k=golayOne) : ∃ q : ℚ, coordinateQuintic i j k=q • theta :=
  (scalar_phases_of_cocode_covariance _ _ (fun d => coordinateQuintic_cocode d i j k)).2 h

end Atlas.Fischer
