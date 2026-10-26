import Atlas.Rudvalis.BinaryGroupOrder
import Atlas.LinearGroups.Elementary

/-! Two literal Version 33 matrices generate the Fano linear group. -/
namespace Atlas.Rudvalis
open Matrix Matrix.SpecialLinearGroup

def binaryPMatrix : Matrix (Fin 3) (Fin 3) Bit := !![1,1,0; 0,1,1; 1,0,0]
def binaryRMatrix : Matrix (Fin 3) (Fin 3) Bit := !![1,0,0; 0,1,0; 1,0,1]

def binaryPSL : Matrix.SpecialLinearGroup (Fin 3) Bit := ⟨binaryPMatrix,by decide +kernel⟩
def binaryRSL : Matrix.SpecialLinearGroup (Fin 3) Bit := ⟨binaryRMatrix,by decide +kernel⟩

noncomputable def binarySLToLinear : Matrix.SpecialLinearGroup (Fin 3) Bit →* (E ≃ₗ[Bit] E) :=
  binaryLinearMatrixEquiv.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
noncomputable def binaryPLinear : E ≃ₗ[Bit] E := binarySLToLinear binaryPSL
noncomputable def binaryRLinear : E ≃ₗ[Bit] E := binarySLToLinear binaryRSL

theorem binaryPLinear_apply (v : E) : binaryPLinear v=binaryPMatrix.mulVec v := rfl
theorem binaryRLinear_apply (v : E) : binaryRLinear v=binaryRMatrix.mulVec v := rfl

theorem binaryPMatrix_columns (j : Fin 3) :
    (fun i => binaryPMatrix i j)=binaryLabel (![5,3,2] j) := by decide +kernel +revert

theorem binaryRMatrix_columns (j : Fin 3) :
    (fun i => binaryRMatrix i j)=binaryLabel (![5,2,4] j) := by decide +kernel +revert

theorem binaryRSL_transvection : binaryRSL=transvection (show (2 : Fin 3)≠0 by decide) 1 := by
  apply Subtype.ext
  decide +kernel

theorem binaryP_R_transvection12 : binaryPSL^2*binaryRSL*binaryPSL*binaryRSL=
    transvection (show (1 : Fin 3)≠2 by decide) 1 := by
  apply Subtype.ext
  decide +kernel

theorem binaryP_R_transvection01 : binaryPSL^4*binaryRSL*binaryPSL^3=
    transvection (show (0 : Fin 3)≠1 by decide) 1 := by
  apply Subtype.ext
  decide +kernel

theorem binaryPR_generate_SL (K : Subgroup (Matrix.SpecialLinearGroup (Fin 3) Bit))
    (hp : binaryPSL∈K) (hr : binaryRSL∈K) : K=⊤ := by
  have h20 : transvection (show (2 : Fin 3)≠0 by decide) (1 : Bit)∈K :=
    binaryRSL_transvection ▸ hr
  have h12 : transvection (show (1 : Fin 3)≠2 by decide) (1 : Bit)∈K :=
    binaryP_R_transvection12 ▸ K.mul_mem (K.mul_mem (K.mul_mem (K.pow_mem hp 2) hr) hp) hr
  have h01 : transvection (show (0 : Fin 3)≠1 by decide) (1 : Bit)∈K :=
    binaryP_R_transvection01 ▸ K.mul_mem (K.mul_mem (K.pow_mem hp 4) hr) (K.pow_mem hp 3)
  have hc {a b : Matrix.SpecialLinearGroup (Fin 3) Bit} (ha : a∈K) (hb : b∈K) :
      a*b*a⁻¹*b⁻¹∈K := K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
  have h02 : transvection (show (0 : Fin 3)≠2 by decide) (1 : Bit)∈K := by
    have h := hc h01 h12
    simpa only [← commutatorElement_def,Atlas.elementary_commutator (i := (0 : Fin 3)) (j := 2) (k := 1) (by decide) (by decide) (by decide),one_mul] using h
  have h10 : transvection (show (1 : Fin 3)≠0 by decide) (1 : Bit)∈K := by
    have h := hc h12 h20
    simpa only [← commutatorElement_def,Atlas.elementary_commutator (i := (1 : Fin 3)) (j := 0) (k := 2) (by decide) (by decide) (by decide),one_mul] using h
  have h21 : transvection (show (2 : Fin 3)≠1 by decide) (1 : Bit)∈K := by
    have h := hc h20 h01
    simpa only [← commutatorElement_def,Atlas.elementary_commutator (i := (2 : Fin 3)) (j := 1) (k := 0) (by decide) (by decide) (by decide),one_mul] using h
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g∈K) _ (fun _ _ => K.mul_mem) g
  intro i j hij a
  have ha : a=0 ∨ a=1 := by decide +kernel +revert
  rcases ha with rfl|rfl
  · simpa using K.one_mem
  · fin_cases i <;> fin_cases j <;> simp_all <;> exact False.elim (hij rfl)

theorem binarySLToLinear_surjective : Function.Surjective binarySLToLinear := by
  intro g
  let A := binaryLinearMatrixEquiv.symm g
  have hd : (A.val).det=1 := by
    have hn := Matrix.GeneralLinearGroup.det_ne_zero A
    have hb : ∀ x : Bit, x≠0 → x=1 := by decide +kernel
    exact hb _ hn
  refine ⟨⟨A.val,hd⟩,?_⟩
  change binaryLinearMatrixEquiv (Matrix.SpecialLinearGroup.toGL ⟨A.val,hd⟩)=g
  have he : Matrix.SpecialLinearGroup.toGL ⟨A.val,hd⟩=A := Units.ext rfl
  rw [he]
  exact binaryLinearMatrixEquiv.apply_symm_apply g

theorem binaryPR_generate (K : Subgroup (E ≃ₗ[Bit] E))
    (hp : binaryPLinear∈K) (hr : binaryRLinear∈K) : K=⊤ := by
  have ht : K.comap binarySLToLinear=⊤ := binaryPR_generate_SL _ hp hr
  apply top_unique
  intro g _
  obtain ⟨s,rfl⟩ := binarySLToLinear_surjective g
  change s∈K.comap binarySLToLinear
  rw [ht]
  trivial

end Atlas.Rudvalis
