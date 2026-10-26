import Atlas.LinearGroups.F4.ParabolicMarkedPoint

/-! The optional one-step opposition criterion does not apply to the Albert
point action. The obstruction is an intrinsic totally isotropic image space;
no group-order or simplicity theorem is used. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

/-- The trace-zero image of cross multiplication by C₀ is totally isotropic. -/
theorem parabolicImageZero_tracePairing {x y : Carrier F}
    (hx : x∈parabolicImageZero (F:=F)) (hy : y∈parabolicImageZero (F:=F)) :
    tracePairing x y=0 := by
  obtain ⟨u,hu⟩ := hx.1
  obtain ⟨v,hv⟩ := hy.1
  subst x
  subst y
  have ht : trace (parabolicCross u)=0 := hx.2
  have hu7 : u.2 2 7=0 := by
    simpa [parabolicCross_coordinates,trace] using ht
  rw [tracePairing_coordinates,parabolicCross_coordinates,parabolicCross_coordinates]
  simp [Fin.sum_univ_succ,hu7]

/-- The A₀ point belongs to the intrinsic trace-zero image at C₀. -/
theorem baseVector_mem_parabolicImageZero : baseVector (F:=F)∈parabolicImageZero := by
  refine ⟨?_,?_⟩
  · refine ⟨(0,![0,![0,0,0,-1,0,0,0,0],0]),?_⟩
    rw [parabolicCross_coordinates]
    apply Prod.ext
    · ext i; fin_cases i <;> simp [baseVector]
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp [baseVector,SplitOctonion.basisVector,Pi.single_apply]
  · exact baseVector_trace

/-- These two white vectors represent distinct projective points. -/
theorem baseVector_ne_smul_parabolicVector (t : F) :
    baseVector (F:=F)≠t • parabolicVector := by
  intro h
  have hc := congrArg (fun z : Carrier F => z.2 0 0) h
  simpa [baseVector,parabolicVector,SplitOctonion.basisVector] using hc

/-- Every element fixing C₀'s projective point moves A₀ to a vector orthogonal
 to A₀. Thus the proposed one-step move to opposition cannot exist. -/
theorem parabolicStabilizer_baseVector_pairing_zero
    (g : parabolicPointStabilizer (F:=F)) :
    tracePairing baseVector (g.val.val baseVector)=0 :=
  parabolicImageZero_tracePairing baseVector_mem_parabolicImageZero
    (parabolicPointStabilizer_preserves_imageZero g baseVector_mem_parabolicImageZero)

theorem no_one_step_opposite_move_at_parabolicPoint :
    ¬ ∃ g : parabolicPointStabilizer (F:=F),
      tracePairing baseVector (g.val.val baseVector)≠0 := by
  rintro ⟨g,hg⟩
  exact hg (parabolicStabilizer_baseVector_pairing_zero g)

end Atlas.F4
