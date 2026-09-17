import Atlas.Algebra.IcosianOrderParity
import Atlas.Algebra.IcosianCoordinateExhaustion

namespace Atlas.Algebra
open Atlas.Codes
open scoped Quaternion QuadraticAlgebra

theorem icosianCoordinatesQuaternion_injective :
    Function.Injective icosianCoordinatesQuaternion := by
  intro v w h
  have h0 := congrArg (fun q : IcosianQuaternion => q.re.re) h
  have h1 := congrArg (fun q : IcosianQuaternion => q.re.im) h
  have h2 := congrArg (fun q : IcosianQuaternion => q.imI.re) h
  have h3 := congrArg (fun q : IcosianQuaternion => q.imI.im) h
  have h4 := congrArg (fun q : IcosianQuaternion => q.imJ.re) h
  have h5 := congrArg (fun q : IcosianQuaternion => q.imJ.im) h
  have h6 := congrArg (fun q : IcosianQuaternion => q.imK.re) h
  have h7 := congrArg (fun q : IcosianQuaternion => q.imK.im) h
  simp only [icosianCoordinatesQuaternion,div_left_inj' (by norm_num : (2 : ℚ)≠0),
    Int.cast_inj] at h0 h1 h2 h3 h4 h5 h6 h7
  funext i
  fin_cases i <;> assumption

/-- Exhaustion of actual integral norm-one quaternions, rather than an assumed unit list. -/
theorem icosianNormOne_exhaust {x : IcosianQuaternion}
    (hx : IsIcosian x) (hn : icosianNorm x=1) :
    ∃ v ∈ icosianNormOneCoordinates,icosianCoordinatesQuaternion v=x := by
  obtain ⟨v,hv,rfl⟩ := isIcosian_has_parity_coordinates hx
  rw [icosianCoordinatesQuaternion_norm] at hn
  have hr := congrArg QuadraticAlgebra.re hn
  have hi := congrArg QuadraticAlgebra.im hn
  simp only [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one] at hr hi
  have hnorm : icosianCoordinateNorm v=4 := by exact_mod_cast (show (icosianCoordinateNorm v : ℚ)=4 by linarith)
  have htau : icosianCoordinateTau v=0 := by exact_mod_cast (show (icosianCoordinateTau v : ℚ)=0 by linarith)
  exact ⟨v,Finset.mem_filter.mpr ⟨icosianShortCoordinates_exhaust v hnorm hv,htau⟩,rfl⟩

end Atlas.Algebra
