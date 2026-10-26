import Atlas.LinearGroups.F4.PointFlag
import Atlas.LinearGroups.Orthogonal.Basic

/-! The concrete seven-dimensional quadratic layer at C₀. This module asserts
neither an image theorem for the point stabilizer nor an identification with Spin₇. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def parabolicCrossTrace : Submodule F (Carrier F) :=
  (parabolicCross (F:=F)).ker ⊓ (parabolicTrace (F:=F)).ker

def parabolicSevenCoordinates : Carrier F →ₗ[F] Atlas.Orthogonal.VectorB 3 F where
  toFun x := (Sum.elim ![x.2 2 1,x.2 2 2,x.2 2 3] ![x.2 2 6,x.2 2 5,x.2 2 4],x.1 0)
  map_add' x y := by
    apply Prod.ext
    · ext i; cases i with
      | inl i => fin_cases i <;> rfl
      | inr i => fin_cases i <;> rfl
    · rfl
  map_smul' s x := by
    apply Prod.ext
    · ext i; cases i with
      | inl i => fin_cases i <;> rfl
      | inr i => fin_cases i <;> rfl
    · rfl

def parabolicSevenMap : (parabolicCrossTrace (F:=F)) →ₗ[F] Atlas.Orthogonal.VectorB 3 F :=
  parabolicSevenCoordinates.comp parabolicCrossTrace.subtype

theorem parabolicSevenMap_surjective : Function.Surjective (parabolicSevenMap (F:=F)) := by
  rintro ⟨v,a⟩
  let x : Carrier F := (![a,-a,0],
    ![0,0,![0,v (.inl 0),v (.inl 1),v (.inl 2),v (.inr 2),v (.inr 1),v (.inr 0),0]])
  have hx : x∈parabolicCrossTrace := by
    refine ⟨(parabolicCross_eq_zero_iff x).mpr ?_,?_⟩
    · simp [x]
    · change trace x=0
      simp [trace,x]
  refine ⟨⟨x,hx⟩,?_⟩
  apply Prod.ext
  · ext i; cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl
  · rfl

theorem parabolicSevenMap_form (x : parabolicCrossTrace (F:=F)) :
    Atlas.Orthogonal.formB 3 F (parabolicSevenMap x) = -quadraticTrace x.val := by
  have hk := (parabolicCross_eq_zero_iff x.val).mp x.prop.1
  have ht : x.val.1 0+x.val.1 1+x.val.1 2=0 := x.prop.2
  have hb : x.val.1 1 = -x.val.1 0 := by rw [hk.1,add_zero] at ht; linear_combination ht
  simp only [Atlas.Orthogonal.formB_apply,Atlas.Orthogonal.formD_apply,
    parabolicSevenMap,parabolicSevenCoordinates,LinearMap.coe_comp,Function.comp_apply,
    Submodule.subtype_apply,Fin.sum_univ_succ]
  simp [quadraticTrace,SplitOctonion.norm,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,
    hk.2.2.2.2.1,hk.2.2.2.2.2.1,hk.2.2.2.2.2.2.1,hk.2.2.2.2.2.2.2.1,
    hk.2.2.2.2.2.2.2.2.1,hk.2.2.2.2.2.2.2.2.2,hb]
  ring

end Atlas.F4
