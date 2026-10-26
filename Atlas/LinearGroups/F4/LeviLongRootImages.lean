import Atlas.LinearGroups.F4.LeviLongRootBridge
import Atlas.LinearGroups.F4.LeviRootImages

/-! The twelve actual long roots in the marked B₃ subsystem induce the
standard two-shear Siegel transformations on the quadratic quotient. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def leviLongDirection : Fin 12 → Fin 6 := ![0,0,5,5,0,3,2,3,1,3,2,3]
def leviLongParameterDirection : Fin 12 → Fin 6 := ![1,4,1,4,2,0,5,5,2,1,4,4]
def leviLongParameterSign : Fin 12 → ℤ := ![1,-1,-1,1,-1,-1,-1,1,1,1,1,-1]

def leviLongParameter (k : Fin 12) (t : F) : Atlas.Orthogonal.VectorB 3 F :=
  ((leviLongParameterSign k : F)*t) • leviSingularDirection (leviLongParameterDirection k)

set_option maxHeartbeats 2000000 in
theorem leviLongRoot_fixes (k : Fin 12) (t : F) :
    (longRoot (leviLongLabel k) t).val parabolicVector=parabolicVector := by
  rw [longRoot_leviLongApply]
  fin_cases k
  all_goals
    apply Prod.ext
    · ext i; fin_cases i <;> simp [leviLongApply,parabolicVector]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [leviLongApply,parabolicVector]

def leviLongRoot (k : Fin 12) (t : F) : parabolicPointStabilizer (F:=F) :=
  ⟨longRoot (leviLongLabel k) t,by
    apply (mem_parabolicPointStabilizer_iff _).mpr
    exact ⟨1,by simpa using leviLongRoot_fixes k t⟩⟩

set_option maxHeartbeats 1000000 in
theorem leviLongParameter_perp (k : Fin 12) (t : F) :
    (Atlas.Orthogonal.formB 3 F).polarBilin (leviSingularDirection (leviLongDirection k))
      (leviLongParameter k t)=0 := by
  fin_cases k <;>
    simp [Atlas.Orthogonal.polarB_apply,Atlas.Orthogonal.polarD_apply,QuadraticMap.polar,
      leviLongParameter,leviLongDirection,leviLongParameterDirection,leviLongParameterSign,
      leviSingularDirection,leviShortDirection,Fin.sum_univ_succ,Pi.single_apply]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem leviLongRoot_quotient_apply (k : Fin 12) (t : F)
    (v : Atlas.Orthogonal.VectorB 3 F) :
    (parabolicOrthogonalHom (leviLongRoot k t)).val v=
      Atlas.Quadratic.siegel (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection (leviLongDirection k)) (leviLongParameter k t) v := by
  change parabolicSevenEquiv (leviLongRoot k t) v=_
  rw [←leviSevenSection_coordinates v,parabolicSevenEquiv_apply,leviSevenSection_coordinates]
  change parabolicSevenCoordinates ((longRoot (leviLongLabel k) t).val
    (leviSevenSection v).val)=_
  rw [longRoot_leviLongApply]
  fin_cases k
  all_goals
    apply Prod.ext
    · ext j; cases j with
      | inl j => fin_cases j <;>
          simp [parabolicSevenCoordinates,leviSevenSection,leviLongApply,
            Atlas.Quadratic.siegel,Atlas.Orthogonal.polarB_apply,Atlas.Orthogonal.polarD_apply,QuadraticMap.polar,
            Atlas.Orthogonal.formD_apply,leviSingularDirection,leviShortDirection,
            leviLongParameter,leviLongDirection,leviLongParameterDirection,leviLongParameterSign,
            Pi.single_apply,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;> simp
      | inr j => fin_cases j <;>
          simp [parabolicSevenCoordinates,leviSevenSection,leviLongApply,
            Atlas.Quadratic.siegel,Atlas.Orthogonal.polarB_apply,Atlas.Orthogonal.polarD_apply,QuadraticMap.polar,
            Atlas.Orthogonal.formD_apply,leviSingularDirection,leviShortDirection,
            leviLongParameter,leviLongDirection,leviLongParameterDirection,leviLongParameterSign,
            Pi.single_apply,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;> simp
    · simp [parabolicSevenCoordinates,leviSevenSection,leviLongApply,
        Atlas.Quadratic.siegel,Atlas.Orthogonal.polarB_apply,Atlas.Orthogonal.polarD_apply,QuadraticMap.polar,
        Atlas.Orthogonal.formD_apply,leviSingularDirection,leviShortDirection,
        leviLongParameter,leviLongDirection,leviLongParameterDirection,leviLongParameterSign,
        Pi.single_apply,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;> simp

theorem leviLongRoot_quotient (k : Fin 12) (t : F) :
    parabolicOrthogonalHom (leviLongRoot k t)=
      Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection (leviLongDirection k)) (leviLongParameter k t)
        (leviSingularDirection_singular _) (leviLongParameter_perp k t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  exact leviLongRoot_quotient_apply k t

theorem leviLongRoot_quotient_mem_elementary (k : Fin 12) (t : F) :
    parabolicOrthogonalHom (leviLongRoot k t)∈
      Atlas.Orthogonal.elementarySubgroup (Atlas.Orthogonal.formB 3 F) := by
  rw [leviLongRoot_quotient]
  exact Atlas.Orthogonal.siegelElement_mem _ _ _ _ _

end Atlas.F4
