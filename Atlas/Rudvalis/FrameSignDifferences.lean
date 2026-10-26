import Atlas.Rudvalis.FrameMatrixDifferences

namespace Atlas.Rudvalis
open scoped BigOperators

def binaryElementarySL (i j : Fin 3) (hij : i≠j) : Matrix.SpecialLinearGroup (Fin 3) Bit :=
  Matrix.SpecialLinearGroup.transvection hij 1

noncomputable def binaryElementaryLinear (i j : Fin 3) (hij : i≠j) : E ≃ₗ[Bit] E :=
  binarySLToLinear (binaryElementarySL i j hij)

theorem binaryElementaryLinear_apply (i j : Fin 3) (hij : i≠j) (x : E) :
    binaryElementaryLinear i j hij x=(binaryElementaryMatrix i j).mulVec x := by
  change ((binaryElementarySL i j hij).val).mulVec x=_
  rw [binaryElementarySL,Matrix.SpecialLinearGroup.transvection_coe]
  have he : (Matrix.single i j (1 : Bit) : BinaryMatrix)=binaryMatrixUnit i j := by
    have cert : ∀i j : Fin 3,(Matrix.single i j (1 : Bit) : BinaryMatrix)=binaryMatrixUnit i j := by decide +kernel
    exact cert i j
  rw [he]
  rfl

theorem rowSign_elementary_difference (i j : Fin 3) (hij : i≠j) :
    (affineRowSign 0 (basisPoint i).val ∘ linearPointEquiv (binaryElementaryLinear i j hij))-
      affineRowSign 0 (basisPoint i).val=affineRowSign 0 (basisPoint j).val := by
  funext p
  simp only [Pi.sub_apply,Function.comp_apply,affineRowSign,zero_add]
  change dot (basisPoint i).val (binaryElementaryLinear i j hij p.val)-dot (basisPoint i).val p.val=
    dot (basisPoint j).val p.val
  rw [binaryElementaryLinear_apply]
  have cert : ∀i j : Fin 3,i≠j → ∀x : E,
      dot (basisPoint i).val ((binaryElementaryMatrix i j).mulVec x)-dot (basisPoint i).val x=
        dot (basisPoint j).val x := by decide +kernel
  exact cert i j hij p.val

theorem affineRowSign_linear_expansion (v : E) :
    affineRowSign 0 v=∑i : Fin 3,v i • affineRowSign 0 (basisPoint i).val := by
  funext p
  simp only [affineRowSign,zero_add,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,dot_basisPoint]
  rfl

/-- Constants and row-group differences span the actual Hamming sign code. -/
theorem hammingSign_differences_scalar_span (W : Submodule Bit (Point→Bit))
    (h1 : (fun _=>1 : Point→Bit)∈W)
    (hD : ∀g : E ≃ₗ[Bit] E,∀v : E,
      (affineRowSign 0 v ∘ linearPointEquiv g)-affineRowSign 0 v∈W) :
    hammingSignCode≤W := by
  have hb (j : Fin 3) : affineRowSign 0 (basisPoint j).val∈W := by
    obtain ⟨i,hij⟩ := exists_ne j
    rw [←rowSign_elementary_difference i j hij]
    exact hD _ _
  have hv (v : E) : affineRowSign 0 v∈W := by
    rw [affineRowSign_linear_expansion]
    exact W.sum_mem (fun i _=>W.smul_mem _ (hb i))
  intro s hs
  obtain ⟨⟨a,v⟩,he⟩ := affineRowSign_surjective ⟨s,hs⟩
  have he' : affineRowSign a v=s := congrArg Subtype.val he
  rw [←he']
  have heq : affineRowSign a v=a • (fun _=>1 : Point→Bit)+affineRowSign 0 v := by
    funext p; simp [affineRowSign]
  rw [heq]
  exact W.add_mem (W.smul_mem a h1) (hv v)

end Atlas.Rudvalis
