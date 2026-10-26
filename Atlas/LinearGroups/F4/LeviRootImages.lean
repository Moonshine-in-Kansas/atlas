import Atlas.LinearGroups.F4.ParabolicQuotientAction
import Atlas.LinearGroups.F4.ParabolicShortRoots
import Atlas.LinearGroups.Orthogonal.Elementary

/-! Concrete images of the six Levi short roots in the seven-dimensional
quadratic quotient. No assertion of fullness of the parabolic image is made. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def leviShortIndex : Fin 6 → Fin 8 := ![1,2,3,4,5,6]
def leviShortDirection : Fin 6 → Atlas.Orthogonal.Index 3 :=
  ![Sum.inl 0,Sum.inl 1,Sum.inl 2,Sum.inr 2,Sum.inr 1,Sum.inr 0]

def leviSevenSection (v : Atlas.Orthogonal.VectorB 3 F) : parabolicCrossTrace (F:=F) :=
  ⟨(![v.2,-v.2,0],![0,0,
    ![0,v.1 (.inl 0),v.1 (.inl 1),v.1 (.inl 2),v.1 (.inr 2),v.1 (.inr 1),v.1 (.inr 0),0]]),by
    refine ⟨(parabolicCross_eq_zero_iff _).mpr ?_,?_⟩
    · simp
    · change trace _=0
      simp [trace]⟩

theorem leviSevenSection_coordinates (v : Atlas.Orthogonal.VectorB 3 F) :
    parabolicSevenMap (leviSevenSection v)=v := by
  apply Prod.ext
  · ext i; cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl
  · rfl

def leviShortRoot (k : Fin 6) (t : F) : parabolicPointStabilizer (F:=F) :=
  ⟨shortRoot 0 (leviShortIndex k) t,by
    fin_cases k
    · exact shortRoot_mem_parabolicPointStabilizer 1 (by decide +kernel) t
    · exact shortRoot_mem_parabolicPointStabilizer 2 (by decide +kernel) t
    · exact shortRoot_mem_parabolicPointStabilizer 3 (by decide +kernel) t
    · exact shortRoot_mem_parabolicPointStabilizer 4 (by decide +kernel) t
    · exact shortRoot_mem_parabolicPointStabilizer 5 (by decide +kernel) t
    · exact shortRoot_mem_parabolicPointStabilizer 6 (by decide +kernel) t⟩

def leviSingularDirection (k : Fin 6) : Atlas.Orthogonal.VectorB 3 F :=
  (Pi.single (leviShortDirection k) 1,0)

def leviAnisotropicParameter (t : F) : Atlas.Orthogonal.VectorB 3 F := (0,t)

theorem leviSingularDirection_singular (k : Fin 6) :
    Atlas.Orthogonal.formB 3 F (leviSingularDirection k)=0 := by
  fin_cases k <;>
    simp [leviSingularDirection,leviShortDirection,Atlas.Orthogonal.formD_apply,Fin.sum_univ_succ]

theorem leviSingularDirection_perp (k : Fin 6) (t : F) :
    (Atlas.Orthogonal.formB 3 F).polarBilin (leviSingularDirection k)
      (leviAnisotropicParameter t)=0 := by
  simp [Atlas.Orthogonal.polarB_apply,Atlas.Orthogonal.polarD_apply,QuadraticMap.polar,
    leviSingularDirection,leviAnisotropicParameter]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- Each short root induces the Siegel transformation in its singular
coordinate direction with anisotropic parameter `t`. This includes characteristic two. -/
theorem leviShortRoot_quotient_apply (k : Fin 6) (t : F)
    (v : Atlas.Orthogonal.VectorB 3 F) :
    (parabolicOrthogonalHom (leviShortRoot k t)).val v=
      Atlas.Quadratic.siegel (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection k) (leviAnisotropicParameter t) v := by
  change parabolicSevenEquiv (leviShortRoot k t) v=_
  rw [←leviSevenSection_coordinates v,parabolicSevenEquiv_apply,leviSevenSection_coordinates]
  change parabolicSevenCoordinates (Atlas.Albert.shortRootLinear (leviShortIndex k) t
    (leviSevenSection v).val)=_
  fin_cases k
  all_goals
    apply Prod.ext
    · ext j; cases j with
      | inl j => fin_cases j <;>
          simp [parabolicSevenCoordinates,leviSevenSection,leviShortIndex,
            Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
            Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
            Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
            Atlas.Quadratic.siegel,Atlas.Orthogonal.polarB_apply,Atlas.Orthogonal.polarD_apply,QuadraticMap.polar,
            Atlas.Orthogonal.formD_apply,leviSingularDirection,leviShortDirection,
            leviAnisotropicParameter,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;> simp
      | inr j => fin_cases j <;>
          simp [parabolicSevenCoordinates,leviSevenSection,leviShortIndex,
            Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
            Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
            Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
            Atlas.Quadratic.siegel,Atlas.Orthogonal.polarB_apply,Atlas.Orthogonal.polarD_apply,QuadraticMap.polar,
            Atlas.Orthogonal.formD_apply,leviSingularDirection,leviShortDirection,
            leviAnisotropicParameter,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;> simp
    · simp [parabolicSevenCoordinates,leviSevenSection,leviShortIndex,
        Atlas.Albert.shortRootLinear,Atlas.Albert.shortRootFormula,
        Atlas.SplitOctonion.basisVector,Pi.single_apply,Atlas.SplitOctonion.mul,
        Atlas.SplitOctonion.conjugate,Atlas.SplitOctonion.trace,Atlas.SplitOctonion.unit,
        Atlas.Quadratic.siegel,Atlas.Orthogonal.polarB_apply,Atlas.Orthogonal.polarD_apply,QuadraticMap.polar,
        Atlas.Orthogonal.formD_apply,leviSingularDirection,leviShortDirection,
        leviAnisotropicParameter,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring_nf <;> simp

theorem leviShortRoot_quotient (k : Fin 6) (t : F) :
    parabolicOrthogonalHom (leviShortRoot k t)=
      Atlas.Orthogonal.siegelElement (Atlas.Orthogonal.formB 3 F)
        (leviSingularDirection k) (leviAnisotropicParameter t)
        (leviSingularDirection_singular k) (leviSingularDirection_perp k t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  exact leviShortRoot_quotient_apply k t

theorem leviShortRoot_quotient_mem_elementary (k : Fin 6) (t : F) :
    parabolicOrthogonalHom (leviShortRoot k t)∈
      Atlas.Orthogonal.elementarySubgroup (Atlas.Orthogonal.formB 3 F) := by
  rw [leviShortRoot_quotient]
  exact Atlas.Orthogonal.siegelElement_mem _ _ _ _ _

end Atlas.F4
