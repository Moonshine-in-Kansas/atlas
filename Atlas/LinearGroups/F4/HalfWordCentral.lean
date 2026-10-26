import Atlas.LinearGroups.F4.HalfRootCentralLayer
import Atlas.LinearGroups.F4.ShortRadicalWord

/-! The bilinear part of the actual eight-half-root word action.
The remaining constant is the word's value at the literal C₇ base vector. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def halfWordBilinear (t z : Fin 8 → F) : Fin 7 → F :=
  ∑ i : Fin 8,t i • halfRootCentralApply i z

def halfWordBilinearMap : (Fin 8 → F) →ₗ[F] ((Fin 8 → F) →ₗ[F] (Fin 7 → F)) where
  toFun t := ∑ i : Fin 8,t i • halfRootCentralLinear i
  map_add' t u := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a t := by simp [smul_smul,Finset.smul_sum]

theorem halfWordBilinearMap_apply (t z : Fin 8 → F) :
    halfWordBilinearMap t z=halfWordBilinear t z := by
  simp [halfWordBilinearMap,halfWordBilinear,halfRootCentralLinear]

theorem halfWordList_central_difference (t : Fin 8 → F) (l : List (Fin 8))
    (x y : Atlas.Albert.Carrier F) (hxy : x.2 2 7=y.2 2 7) :
    centralSevenCoordinates ((halfWordList t l).val x) -
      centralSevenCoordinates ((halfWordList t l).val y) =
        centralSevenCoordinates x-centralSevenCoordinates y +
          (l.map (fun i=> t i • halfRootCentralApply i
            (oppositeLowerCoordinates x-oppositeLowerCoordinates y))).sum := by
  induction l generalizing x y with
  | nil => simp [halfWordList]
  | cons i l ih =>
    have hx := halfWordList_lower t l x
    have hy := halfWordList_lower t l y
    have hl : oppositeLowerCoordinates ((halfWordList t l).val x) -
        oppositeLowerCoordinates ((halfWordList t l).val y) =
          oppositeLowerCoordinates x-oppositeLowerCoordinates y := by
      rw [hx.2,hy.2,hxy]
      abel
    have ht : halfRootCentralApply i (oppositeLowerCoordinates ((halfWordList t l).val x)) -
        halfRootCentralApply i (oppositeLowerCoordinates ((halfWordList t l).val y)) =
          halfRootCentralApply i (oppositeLowerCoordinates x-oppositeLowerCoordinates y) := by
      change (halfRootCentralLinear (R := F) i) _-(halfRootCentralLinear (R := F) i) _=(halfRootCentralLinear (R := F) i) _
      rw [←map_sub,hl]
    change centralSevenCoordinates ((halfRoot i (t i)).val ((halfWordList t l).val x)) -
      centralSevenCoordinates ((halfRoot i (t i)).val ((halfWordList t l).val y)) = _
    rw [halfRoot_central,halfRoot_central]
    calc
      _ = (centralSevenCoordinates ((halfWordList t l).val x) -
            centralSevenCoordinates ((halfWordList t l).val y)) +
          t i • (halfRootCentralApply i (oppositeLowerCoordinates ((halfWordList t l).val x)) -
            halfRootCentralApply i (oppositeLowerCoordinates ((halfWordList t l).val y))) := by
              rw [smul_sub]
              abel
      _ = _ := by
        rw [ih x y hxy,ht]
        simp only [List.map_cons,List.sum_cons]
        abel

theorem halfWord_central_difference (t : Fin 8 → F) (x y : Atlas.Albert.Carrier F)
    (hxy : x.2 2 7=y.2 2 7) :
    centralSevenCoordinates ((halfWord t).val x)-centralSevenCoordinates ((halfWord t).val y) =
      centralSevenCoordinates x-centralSevenCoordinates y +
        halfWordBilinear t (oppositeLowerCoordinates x-oppositeLowerCoordinates y) := by
  simpa only [halfWord,←Fin.sum_univ_def,halfWordBilinear] using
    halfWordList_central_difference t (List.finRange 8) x y hxy

/-- The literal C₇ basis vector, independently of any chart equivalence. -/
def halfWordBaseVector : Atlas.Albert.Carrier F :=
  (0,![0,0,![0,0,0,0,0,0,0,1]])

theorem halfWordBaseVector_lower : oppositeLowerCoordinates (halfWordBaseVector (F := F))=0 := by
  ext i; fin_cases i <;> rfl

theorem halfWordBaseVector_central : centralSevenCoordinates (halfWordBaseVector (F := F))=0 := by
  ext i; fin_cases i <;> simp [halfWordBaseVector,centralSevenCoordinates]

theorem halfWord_central_chart (t : Fin 8 → F) (x : Atlas.Albert.Carrier F)
    (hx : x.2 2 7=1) :
    centralSevenCoordinates ((halfWord t).val x)=centralSevenCoordinates x+
      halfWordBilinear t (oppositeLowerCoordinates x)+
        centralSevenCoordinates ((halfWord t).val halfWordBaseVector) := by
  have h := halfWord_central_difference t x halfWordBaseVector hx
  rw [halfWordBaseVector_central,halfWordBaseVector_lower,sub_zero,sub_zero] at h
  exact sub_eq_iff_eq_add.mp h

end Atlas.F4
