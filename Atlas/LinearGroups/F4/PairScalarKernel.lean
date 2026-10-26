import Atlas.LinearGroups.F4.PairKernelIdentification
import Atlas.LinearGroups.F4.PairStabilizerScales
import Atlas.LinearGroups.F4.RadicalQuotientKernel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! The actual opposite-pair quotient-action kernel is the scalar torus,
with its multiplicative equivalence and exact cardinality. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def scalarParabolic (a : Fˣ) : parabolicPointStabilizer (F:=F) :=
  ⟨scalarTorus a,(mem_parabolicPointStabilizer_iff _).mpr
    ⟨a^2,by simpa only [Units.val_pow_eq_pow_val] using scalarTorus_C0 a⟩⟩

theorem scalarParabolic_character (a : Fˣ) : parabolicLineCharacter (scalarParabolic a)=a^2 := by
  apply Units.ext
  have h := parabolicLineCharacter_action (scalarParabolic a)
  change (scalarTorus a).val parabolicVector=_ at h
  rw [scalarTorus_C0] at h
  have hc := congrArg (fun x : Carrier F=>x.2 2 0) h
  simpa [parabolicVector] using hc.symm

theorem scalarParabolic_mem_pair (a : Fˣ) : scalarParabolic a∈oppositePairStabilizer (F:=F) := by
  change scalarParabolic a • oppositeBaseCell=oppositeBaseCell
  apply Subtype.ext
  rw [oppositeCellParabolicAction_val,scalarParabolic_character,oppositeBaseCell_eq_pairOpposite]
  change (a^2).val • (scalarTorus a).val pairOppositeVector=pairOppositeVector
  rw [scalarTorus_C7,smul_smul]
  simp only [Units.val_pow_eq_pow_val,←mul_pow,Units.mul_inv,one_pow,one_smul]

def scalarPair (a : Fˣ) : oppositePairStabilizer (F:=F) :=
  ⟨scalarParabolic a,scalarParabolic_mem_pair a⟩

theorem scalarTorus_one : scalarTorus (1 : Fˣ)=1 := by
  apply mul_left_cancel (a:=scalarTorus (1 : Fˣ))
  calc scalarTorus (1 : Fˣ)*scalarTorus 1=scalarTorus 1 := by
         simpa using (scalarTorus_mul (1 : Fˣ) 1).symm
       _=scalarTorus 1*1 := (mul_one _).symm

def scalarPairHom : Fˣ →* oppositePairStabilizer (F:=F) where
  toFun := scalarPair
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact scalarTorus_one
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; exact scalarTorus_mul a b

theorem scalarPairHom_injective : Function.Injective (scalarPairHom (F:=F)) := by
  intro a b h
  apply scalarTorus_injective
  exact congrArg (fun x : oppositePairStabilizer (F:=F)=>x.val.val) h

theorem scalarParabolic_seven (a : Fˣ) (x : Carrier F) :
    parabolicSevenCoordinates ((scalarTorus a).val x)=parabolicSevenCoordinates x := by
  rw [scalarTorus_apply]
  apply Prod.ext
  · ext i; cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl
  · rfl

theorem scalarPair_orthogonal (a : Fˣ) : pairOrthogonalHom (scalarPair a)=1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := parabolicSevenMap_surjective v
  change parabolicSevenEquiv (scalarParabolic a) (parabolicSevenMap x)=parabolicSevenMap x
  rw [parabolicSevenEquiv_apply]
  exact scalarParabolic_seven a x.val

theorem scalarPairHom_range : (scalarPairHom (F:=F)).range=pairOrthogonalHom.ker := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact scalarPair_orthogonal a
  · intro g hg
    have hk : parabolicOrthogonalHom g.val=1 := hg
    obtain ⟨a,ha⟩ := pairKernel_eq_scalarTorus g.val (parabolicLineCharacter g.val)
      (pairStabilizer_positive_scale g) (pairStabilizer_opposite_scale g) hk
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact ha.symm

def scalarPairKernelEquiv : Fˣ ≃* (pairOrthogonalHom (F:=F)).ker :=
  (MonoidHom.ofInjective scalarPairHom_injective).trans (MulEquiv.subgroupCongr scalarPairHom_range)

theorem pairOrthogonalHom_kernel_card [Finite F] :
    Nat.card (pairOrthogonalHom (F:=F)).ker=Nat.card F-1 := by
  rw [←Nat.card_congr scalarPairKernelEquiv.toEquiv,Nat.card_units]

end Atlas.F4
