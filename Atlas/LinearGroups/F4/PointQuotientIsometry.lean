import Atlas.LinearGroups.F4.PointQuadraticQuotient

/-! Identification of the intrinsic middle quotient with the split 7-space.
The quadratic form is descended from minus the Albert quadratic trace. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem parabolicCross_square (x : Carrier F) :
    parabolicCross (parabolicCross x) = -trace (parabolicCross x) • parabolicVector := by
  simp only [parabolicCross_coordinates]
  apply Prod.ext
  · ext i; fin_cases i <;> simp [parabolicVector,trace]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [parabolicVector,trace]

theorem parabolicImageZero_le_crossTrace :
    parabolicImageZero (F:=F) ≤ parabolicCrossTrace := by
  intro x hx
  refine ⟨?_,hx.2⟩
  obtain ⟨y,rfl⟩ := hx.1
  have ht : trace (parabolicCross y)=0 := hx.2
  change parabolicCross (parabolicCross y)=0
  rw [parabolicCross_square,ht,neg_zero,zero_smul]

theorem parabolicSevenCoordinates_zero_iff (x : Carrier F) :
    parabolicSevenCoordinates x=0 ↔ x.1 0=0 ∧ x.2 2 1=0 ∧ x.2 2 2=0 ∧
      x.2 2 3=0 ∧ x.2 2 4=0 ∧ x.2 2 5=0 ∧ x.2 2 6=0 := by
  simp [parabolicSevenCoordinates,Prod.ext_iff,funext_iff,Fin.forall_fin_succ,Sum.forall]
  tauto

theorem parabolicImageZero_iff_seven_zero (x : Carrier F)
    (hx : x∈parabolicCrossTrace) :
    x∈parabolicImageZero ↔ parabolicSevenCoordinates x=0 := by
  constructor
  · rintro ⟨⟨y,rfl⟩,_⟩
    rw [parabolicCross_coordinates]
    apply Prod.ext
    · ext i; cases i with
      | inl i => fin_cases i <;> rfl
      | inr i => fin_cases i <;> rfl
    · rfl
  · intro h
    have hk := (parabolicCross_eq_zero_iff x).mp hx.1
    have hs := (parabolicSevenCoordinates_zero_iff x).mp h
    have ht : trace x=0 := hx.2
    have hb : x.1 1=0 := by simpa [trace,hs.1,hk.1] using ht
    refine ⟨?_,hx.2⟩
    refine ⟨(![0,0,-x.2 2 0],
      ![![0,0,0,0,-x.2 1 0,-x.2 1 1,x.2 1 2,-x.2 1 4],
        ![0,0,0,-x.2 0 0,0,x.2 0 1,-x.2 0 2,-x.2 0 3],0]),?_⟩
    rw [parabolicCross_coordinates]
    apply Prod.ext
    · ext i; fin_cases i <;> simp_all
    · ext i j; fin_cases i <;> fin_cases j <;> simp_all

def parabolicMiddleSubspace : Submodule F (parabolicCrossTrace (F:=F)) :=
  (parabolicImageZero (F:=F)).comap (parabolicCrossTrace (F:=F)).subtype

theorem parabolicSevenMap_ker :
    (parabolicSevenMap (F:=F)).ker=parabolicMiddleSubspace := by
  ext x
  exact (parabolicImageZero_iff_seven_zero x.val x.prop).symm

def parabolicMiddleQuotientEquiv :
    ((parabolicCrossTrace (F:=F)) ⧸ (parabolicMiddleSubspace (F:=F))) ≃ₗ[F]
      Atlas.Orthogonal.VectorB 3 F :=
  (Submodule.quotEquivOfEq _ _ parabolicSevenMap_ker.symm).trans
    ((parabolicSevenMap (F:=F)).quotKerEquivOfSurjective parabolicSevenMap_surjective)

@[simp] theorem parabolicMiddleQuotientEquiv_mk (x : parabolicCrossTrace (F:=F)) :
    parabolicMiddleQuotientEquiv (F:=F) (Submodule.Quotient.mk x)=parabolicSevenMap x := rfl

def parabolicMiddleQuadraticForm :
    QuadraticForm F ((parabolicCrossTrace (F:=F)) ⧸ (parabolicMiddleSubspace (F:=F))) :=
  (Atlas.Orthogonal.formB 3 F).comp parabolicMiddleQuotientEquiv.toLinearMap

theorem parabolicMiddleQuadraticForm_mk (x : parabolicCrossTrace (F:=F)) :
    parabolicMiddleQuadraticForm (F:=F) (Submodule.Quotient.mk x) = -quadraticTrace x.val :=
  parabolicSevenMap_form x

end Atlas.F4
