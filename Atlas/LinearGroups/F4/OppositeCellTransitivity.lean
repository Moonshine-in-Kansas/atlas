import Atlas.Algebra.Albert.OppositeChart
import Atlas.LinearGroups.F4.ShortRadicalWord
import Atlas.LinearGroups.F4.CentralSeven

/-! Actual transitivity of the marked-point stabilizer on its opposite affine cell.
The element is an explicit product of eight half-roots and seven central roots. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem oppositeCell_coordinate_ext (x y : OppositeCell F)
    (hl : oppositeLowerCoordinates x.val=oppositeLowerCoordinates y.val)
    (hc : centralSevenCoordinates x.val=centralSevenCoordinates y.val) : x=y := by
  apply (oppositeCellEquiv (F:=F)).symm.injective
  apply Prod.ext
  · have h := congrFun hc 6
    change -x.val.1 0 = -y.val.1 0 at h
    exact neg_injective h
  · apply Prod.ext
    · ext i; fin_cases i
      · exact congrFun hl 0
      · exact congrFun hl 1
      · exact congrFun hl 2
      · exact congrFun hl 3
    · apply Prod.ext
      · ext i; fin_cases i
        · exact congrFun hl 4
        · exact congrFun hl 5
        · exact congrFun hl 6
        · exact congrFun hl 7
      · ext i; fin_cases i
        · exact congrFun hc 0
        · exact congrFun hc 2
        · exact congrFun hc 4
        · have h := congrFun hc 5
          change -x.val.2 2 4 = -y.val.2 2 4 at h
          exact neg_injective h
        · have h := congrFun hc 3
          change -x.val.2 2 5 = -y.val.2 2 5 at h
          exact neg_injective h
        · have h := congrFun hc 1
          change -x.val.2 2 6 = -y.val.2 2 6 at h
          exact neg_injective h

def halfWordOpposite (t : Fin 8→F) (x : OppositeCell F) : OppositeCell F :=
  ⟨(halfWord t).val x.val,by
    refine ⟨?_,?_,?_⟩
    · rw [stabilizer_adjoint,x.prop.1,map_zero]
    · rw [stabilizer_trace,x.prop.2.1]
    · exact (halfWord_lower t x.val).1.trans x.prop.2.2⟩

def centralSevenOpposite (p : Fin 7→F) (x : OppositeCell F) : OppositeCell F :=
  ⟨(centralSeven p).val x.val,by
    refine ⟨?_,?_,?_⟩
    · rw [stabilizer_adjoint,x.prop.1,map_zero]
    · rw [stabilizer_trace,x.prop.2.1]
    · exact (centralSeven_C7 p x.val).trans x.prop.2.2⟩

theorem oppositeCell_transitive (x y : OppositeCell F) :
    ∃g : parabolicPointStabilizer (F:=F),g.val.val x.val=y.val := by
  let t : Fin 8→F := oppositeLowerCoordinates y.val-oppositeLowerCoordinates x.val
  let z := halfWordOpposite t x
  have hz : oppositeLowerCoordinates z.val=oppositeLowerCoordinates y.val := by
    have h := (halfWord_lower t x.val).2
    rw [x.prop.2.2] at h
    change oppositeLowerCoordinates ((halfWord t).val x.val)=_
    rw [h]
    ext i
    simp [t]
  let p : Fin 7→F := centralSevenCoordinates y.val-centralSevenCoordinates z.val
  have he : centralSevenOpposite p z=y := by
    apply oppositeCell_coordinate_ext
    · change negativeSpinCoordinates (centralSevenApply p z.val)=_
      rw [centralSeven_negative]
      exact hz
    · change centralSevenCoordinates (centralSevenApply p z.val)=_
      rw [centralSeven_coordinates_chart p z.val z.prop.2.2]
      dsimp [p]
      abel
  refine ⟨⟨centralSeven p*halfWord t,
    (parabolicPointStabilizer (F:=F)).mul_mem
      (centralSeven_mem_parabolicPointStabilizer p) (halfWord_mem_parabolic t)⟩,?_⟩
  exact congrArg Subtype.val he

def oppositeBaseCell : OppositeCell F := oppositeCellEquiv (F:=F) (0,0,0,0)

theorem oppositeBaseCell_coordinates :
    (oppositeBaseCell (F:=F)).val=(0,![0,0,![0,0,0,0,0,0,0,1]]) := by
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [oppositeBaseCell,oppositeCellEquiv,oppositeZeroChart,oppositeChart,oppositeDiagonalC]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [oppositeBaseCell,oppositeCellEquiv,oppositeZeroChart,oppositeChart,
        oppositeDiagonalC,oppositeA,oppositeB,oppositeC]

theorem oppositeCell_from_base (x : OppositeCell F) :
    ∃g : Model F,g.val (0,![0,0,![0,0,0,0,0,0,0,1]])=x.val := by
  obtain ⟨g,hg⟩ := oppositeCell_transitive oppositeBaseCell x
  exact ⟨g.val,by simpa only [oppositeBaseCell_coordinates] using hg⟩

end Atlas.F4
