import Atlas.LinearGroups.F4.NearVectorCount
import Atlas.LinearGroups.F4.NearPointEscape
import Atlas.LinearAlgebra.ProjectiveConeCount

/-! The cardinality of the actual near point stratum, excluding the marked point.
The count comes from its split quadratic cone, independently of group order. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

def NearPoints := {x : WhiteZeroPoints F //
  x.val.rep∈parabolicImageZero (F:=F) ∧ x≠parabolicPoint}

private def nearCone (x : Carrier F) : Prop :=
  x∈parabolicImageZero (F:=F) ∧ nearSpinCoordinates x≠0 ∧ adjoint x=0

private theorem nearSpinCoordinates_smul (t : F) (x : Carrier F) :
    nearSpinCoordinates (t • x)=t • nearSpinCoordinates x := by
  ext i
  fin_cases i <;> simp [nearSpinCoordinates]

private theorem nearCone_smul (a : Fˣ) (x : Carrier F) :
    nearCone (a • x) ↔ nearCone x := by
  unfold nearCone
  change ((a:F) • x∈parabolicImageZero ∧
    nearSpinCoordinates ((a:F) • x)≠0 ∧ adjoint ((a:F) • x)=0) ↔ _
  rw [Submodule.smul_mem_iff _ a.ne_zero,nearSpinCoordinates_smul,adjoint_smul]
  simp only [smul_eq_zero,a.ne_zero,false_or,pow_ne_zero 2 a.ne_zero]
  rw [smul_ne_zero_iff_right a.ne_zero]

private theorem parabolicPoint_spin_zero :
    nearSpinCoordinates (parabolicPoint (F:=F)).val.rep=0 := by
  obtain ⟨s,hs⟩ := Projectivization.exists_smul_eq_mk_rep F
    (parabolicVector (F:=F)) parabolicVector_ne_zero
  change nearSpinCoordinates (Projectivization.mk F parabolicVector _).rep=0
  rw [←hs]
  change nearSpinCoordinates ((s:F) • (parabolicVector (F := F)))=0
  rw [nearSpinCoordinates_smul]
  simp [nearSpinCoordinates,parabolicVector]

private def nearConePointsEquiv :
    Atlas.LinearAlgebra.ConePoints (F:=F) (nearCone (F := F)) ≃ NearPoints (F:=F) where
  toFun p := ⟨⟨p.val,show trace p.val.rep=0 from p.prop.1.2,p.prop.2.2⟩,
    p.prop.1,by
      intro he
      have hh := congrArg (fun x : WhiteZeroPoints F => nearSpinCoordinates x.val.rep) he
      exact p.prop.2.1 (hh.trans parabolicPoint_spin_zero)⟩
  invFun x := ⟨x.val.val,x.prop.1,by
    intro hz
    exact x.prop.2 (point_eq_parabolic_of_nearSpin_zero x.val x.prop.1 hz),x.val.prop.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def nearNonzeroConeEquiv :
    Atlas.LinearAlgebra.NonzeroCone (nearCone (F:=F)) ≃ NearVectors (F:=F) where
  toFun x := ⟨x.val,x.prop.2⟩
  invFun x := ⟨x.val,by
    intro hz
    apply x.prop.2.1
    rw [hz]
    simp [nearSpinCoordinates],x.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_nearPoints [Finite F] : Nat.card (NearPoints (F:=F)) =
    (Nat.card F * ((Nat.card F^4-1)*(Nat.card F^3+1))) / (Nat.card F-1) := by
  rw [←Nat.card_congr nearConePointsEquiv,
    Atlas.LinearAlgebra.card_conePoints nearCone nearCone_smul,
    Nat.card_congr nearNonzeroConeEquiv,card_nearVectors]

end Atlas.F4
