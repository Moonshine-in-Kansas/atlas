import Atlas.LinearGroups.F4.LeviRootImages
import Atlas.LinearGroups.Orthogonal.DiagonalAction

/-! The actual diagonal torus induces the entire split three-dimensional torus
on the seven-dimensional quadratic quotient. This is not a full image theorem. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def leviDiagonal (d : Fin 3 → Fˣ) : Atlas.Orthogonal.O_B 3 F :=
  ⟨(Atlas.Orthogonal.diagonalLinear d).prodCongr (LinearEquiv.refl F F),by
    intro v
    change Atlas.Orthogonal.formB 3 F (Atlas.Orthogonal.diagonalLinear d v.1,v.2)=
      Atlas.Orthogonal.formB 3 F v
    simp only [Atlas.Orthogonal.formB_apply,Atlas.Orthogonal.diagonalLinear_form]⟩

def leviTorus (t : TorusParameters F) : parabolicPointStabilizer (F:=F) :=
  ⟨diagonalTorus t,diagonalTorus_mem_parabolicPointStabilizer t⟩

def leviTorusParameters (t : TorusParameters F) : Fin 3 → Fˣ :=
  ![t 0*t 1*t 2,t 1*t 2,t 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem leviTorus_quotient (t : TorusParameters F) :
    parabolicOrthogonalHom (leviTorus t)=leviDiagonal (leviTorusParameters t) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change parabolicSevenEquiv (leviTorus t) v=_
  rw [←leviSevenSection_coordinates v,parabolicSevenEquiv_apply,leviSevenSection_coordinates]
  change parabolicSevenCoordinates (torusApply t (leviSevenSection v).val)=
    (Atlas.Orthogonal.diagonalLinear (leviTorusParameters t) v.1,v.2)
  apply Prod.ext
  · ext i; cases i with
    | inl i => fin_cases i <;>
        simp [parabolicSevenCoordinates,leviSevenSection,torusApply,torusScale,weightCharacter,
          RootData.simpleCoefficients,RootData.coordinates,Weights.slotRoot,
          Fin.prod_univ_succ,leviTorusParameters,Atlas.Orthogonal.diagonalLinear,mul_assoc]
    | inr i => fin_cases i <;>
        simp [parabolicSevenCoordinates,leviSevenSection,torusApply,torusScale,weightCharacter,
          RootData.simpleCoefficients,RootData.coordinates,Weights.slotRoot,
          Fin.prod_univ_succ,leviTorusParameters,Atlas.Orthogonal.diagonalLinear,mul_assoc] <;>
          field_simp <;> ring
  · rfl

def leviTorusLift (d : Fin 3 → Fˣ) : TorusParameters F :=
  ![d 0*(d 1)⁻¹,d 1*(d 2)⁻¹,d 2,1]

theorem leviTorusParameters_lift (d : Fin 3 → Fˣ) :
    leviTorusParameters (leviTorusLift d)=d := by
  funext i
  fin_cases i <;> simp [leviTorusParameters,leviTorusLift,mul_assoc]

theorem leviTorusLift_quotient (d : Fin 3 → Fˣ) :
    parabolicOrthogonalHom (leviTorus (leviTorusLift d))=leviDiagonal d := by
  rw [leviTorus_quotient,leviTorusParameters_lift]

theorem leviDiagonal_mem_parabolic_image (d : Fin 3 → Fˣ) :
    leviDiagonal d∈parabolicOrthogonalHom.range :=
  ⟨leviTorus (leviTorusLift d),leviTorusLift_quotient d⟩

end Atlas.F4
