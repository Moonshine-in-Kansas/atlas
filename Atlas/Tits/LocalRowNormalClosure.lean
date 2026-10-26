import Atlas.Tits.LocalRowMatrix
import Atlas.Rudvalis.ReferenceLinearLifts

/-! The actual binary row stabilizer and its small normal quotient. Certificates
involve only its 24 matrices and twelve words in two conjugate elements. -/

namespace Atlas.Tits
open Atlas.Rudvalis
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The actual linear stabilizer of the marked Fano point. -/
def localRowStabilizer : Subgroup (E ≃ₗ[Bit] E) where
  carrier := {A | A (rowLabel 0).val = (rowLabel 0).val}
  one_mem' := rfl
  mul_mem' := by
    intro A B hA hB
    change A (B (rowLabel 0).val) = (rowLabel 0).val
    rw [hB,hA]
  inv_mem' := by
    intro A hA
    change A.symm (rowLabel 0).val = (rowLabel 0).val
    calc
      A.symm (rowLabel 0).val = A.symm (A (rowLabel 0).val) :=
        congrArg A.symm hA.symm
      _ = (rowLabel 0).val := A.symm_apply_apply _

/-- A computational matrix presentation of exactly the same stabilizer. -/
noncomputable def localRowMatrixStabilizer :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) Bit) :=
  localRowStabilizer.comap binarySLToLinear

instance localRowMatrixMemDecidable : DecidablePred (· ∈ localRowMatrixStabilizer) :=
  fun A => inferInstanceAs (Decidable (A.val.mulVec (rowLabel 0).val = (rowLabel 0).val))

instance localRowMatrixFintype : Fintype localRowMatrixStabilizer := Subtype.fintype _

noncomputable def localRowMatrixHom : localRowMatrixStabilizer →* localRowStabilizer where
  toFun A := ⟨binarySLToLinear A.val,A.prop⟩
  map_one' := Subtype.ext (map_one binarySLToLinear)
  map_mul' A B := Subtype.ext (map_mul binarySLToLinear A.val B.val)

theorem localRowMatrixHom_injective : Function.Injective localRowMatrixHom := by
  intro A B h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  have hh := binaryLinearMatrixEquiv.injective he
  apply Subtype.ext
  exact congrArg Units.val hh

theorem localRowMatrixHom_surjective : Function.Surjective localRowMatrixHom := by
  intro A
  obtain ⟨B,hB⟩ := binarySLToLinear_surjective A.val
  refine ⟨⟨B,?_⟩,?_⟩
  · change binarySLToLinear B ∈ localRowStabilizer
    rw [hB]
    exact A.prop
  · exact Subtype.ext hB

noncomputable def localRowMatrixEquiv : localRowMatrixStabilizer ≃* localRowStabilizer :=
  MulEquiv.ofBijective localRowMatrixHom
    ⟨localRowMatrixHom_injective,localRowMatrixHom_surjective⟩

instance localRowStabilizerFinite : Finite localRowStabilizer :=
  Finite.of_surjective localRowMatrixHom localRowMatrixHom_surjective

theorem localRowMatrixStabilizer_card : Nat.card localRowMatrixStabilizer = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem localRowStabilizer_card : Nat.card localRowStabilizer = 24 :=
  (Nat.card_congr localRowMatrixEquiv.toEquiv).symm.trans localRowMatrixStabilizer_card

/-- The concrete order-three row matrix of d⁴. -/
def localRowNMatrix : localRowMatrixStabilizer :=
  ⟨⟨localRowMatrix,by decide +kernel⟩,by
    change localRowMatrix.mulVec (rowLabel 0).val = (rowLabel 0).val
    decide +kernel⟩

/-- The marked row involution R. -/
def localRowRMatrix : localRowMatrixStabilizer :=
  ⟨binaryRSL,by decide +kernel⟩

noncomputable def localRowCMatrix : localRowMatrixStabilizer :=
  localRowRMatrix * localRowNMatrix * localRowRMatrix⁻¹

def localRowWordFactors (i : Fin 12) : List Bool :=
  ![[],[false],[true],[false,false],[false,true],[true,false],[true,true],
    [false,false,true],[false,true,true],[true,false,false],[true,true,false],
    [false,true,true,false]] i

noncomputable def localRowWord (i : Fin 12) : localRowMatrixStabilizer :=
  ((localRowWordFactors i).map fun b => if b then localRowCMatrix else localRowNMatrix).prod

theorem localRowWord_injective : Function.Injective localRowWord := by decide +kernel

/-- Every actual row matrix lies in one of the two exhibited cosets. -/
theorem localRowWord_covers (A : localRowMatrixStabilizer) :
    ∃ i : Fin 12, A = localRowWord i ∨ A = localRowRMatrix * localRowWord i := by
  decide +kernel +revert

theorem localRowWord_mem (H : Subgroup localRowMatrixStabilizer) [H.Normal]
    (hN : localRowNMatrix ∈ H) (i : Fin 12) : localRowWord i ∈ H := by
  have hC : localRowCMatrix ∈ H :=
    (inferInstance : H.Normal).conj_mem _ hN localRowRMatrix
  apply H.list_prod_mem
  intro g hg
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hg
  cases b
  · exact hN
  · exact hC

noncomputable def localRowN : localRowStabilizer := localRowMatrixHom localRowNMatrix
noncomputable def localRowR : localRowStabilizer := localRowMatrixHom localRowRMatrix

theorem localRowN_actual : localRowN.val = codeBlockLinearHom (coupleCodeD ^ 4) := by
  apply LinearEquiv.ext
  intro v
  change localRowMatrix.mulVec v = codeBlockLinearHom (coupleCodeD ^ 4) v
  rw [← binaryLinearMatrix_apply,localCodeN_row_matrix]
  rfl

theorem localRowR_actual : localRowR.val = codeBlockLinearHom codeR := by
  exact codeR_block_image.symm

/-- Surjectivity retains the actual code point-stabilizer lift. -/
noncomputable def codeReferenceRowHom : codeReferenceStabilizer →* localRowStabilizer where
  toFun g := ⟨codeBlockLinearHom g.val,by
    apply coordinateCross_stabilizer_row (rowLabel 0) 0
      (⟨g.val,?_⟩ : MulAction.stabilizer codeGroup (coordinateCross (rowLabel 0,0)))
    have h := g.prop
    change g.val • localReferenceCross = localReferenceCross at h
    change g.val • coordinateCross (rowLabel 0,0) = coordinateCross (rowLabel 0,0)
    simpa only [localReferenceCross_eq] using h⟩
  map_one' := Subtype.ext (map_one codeBlockLinearHom)
  map_mul' g h := Subtype.ext (map_mul codeBlockLinearHom g.val h.val)

theorem codeReferenceRowHom_surjective : Function.Surjective codeReferenceRowHom := by
  intro A
  obtain ⟨g,hg⟩ := codeReferenceStabilizer_linear_lift A.val A.prop
  exact ⟨g,Subtype.ext hg⟩

/-- A normal subgroup containing d⁴ has at least the twelve exhibited elements. -/
theorem localRow_normal_card_lower (H : Subgroup localRowStabilizer) [H.Normal]
    (hN : localRowN ∈ H) : 12 ≤ Nat.card H := by
  let f : Fin 12 → H := fun i =>
    ⟨localRowMatrixHom (localRowWord i),
      localRowWord_mem (H.comap localRowMatrixHom) hN i⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact localRowWord_injective
      (localRowMatrixHom_injective (congrArg Subtype.val hij))
  simpa using Nat.card_le_card_of_injective f hf

/-- The row part of the normal quotient has order at most two. -/
theorem localRow_normal_index_le_two (H : Subgroup localRowStabilizer) [H.Normal]
    (hN : localRowN ∈ H) : H.index ≤ 2 := by
  have hl := localRow_normal_card_lower H hN
  have he := H.card_mul_index
  rw [localRowStabilizer_card] at he
  by_contra hn
  have hi : 3 ≤ H.index := by omega
  have hm := Nat.mul_le_mul hl hi
  omega

/-- Its sole possible nontrivial coset is represented by the actual R. -/
theorem localRow_normal_coset_representatives (H : Subgroup localRowStabilizer) [H.Normal]
    (hN : localRowN ∈ H) (A : localRowStabilizer) :
    ∃ h : H, A = h.val ∨ A = localRowR * h.val := by
  obtain ⟨B,rfl⟩ := localRowMatrixHom_surjective A
  obtain ⟨i,hi | hi⟩ := localRowWord_covers B
  · exact ⟨⟨localRowMatrixHom (localRowWord i),
      localRowWord_mem (H.comap localRowMatrixHom) hN i⟩,
      Or.inl (congrArg localRowMatrixHom hi)⟩
  · refine ⟨⟨localRowMatrixHom (localRowWord i),
      localRowWord_mem (H.comap localRowMatrixHom) hN i⟩,Or.inr ?_⟩
    rw [hi,map_mul]
    rfl

end Atlas.Tits
