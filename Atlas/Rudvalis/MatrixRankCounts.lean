import Atlas.Rudvalis.FourActiveMatrices
import Atlas.Rudvalis.MatrixFibres
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def binaryMatrixLinear (M : BinaryMatrix) : E →ₗ[Bit] E := Matrix.mulVecLin M

theorem binaryMatrixLinear_apply (M : BinaryMatrix) (x : E) :
    binaryMatrixLinear M x = matrixAt M x := rfl

noncomputable def activeVectorEquiv (M : BinaryMatrix) :
    {p : Point // p ∈ nonzeroMatrixBlocks M} ≃ {x : E // binaryMatrixLinear M x ≠ 0} where
  toFun p := ⟨p.val.val, by simpa [nonzeroMatrixBlocks,binaryMatrixLinear_apply] using p.prop⟩
  invFun x := ⟨⟨x.val, by intro h; apply x.prop; simp [h]⟩, by
    simpa [nonzeroMatrixBlocks,binaryMatrixLinear_apply] using x.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem active_card_add_kernel (M : BinaryMatrix) :
    (nonzeroMatrixBlocks M).card + Nat.card (binaryMatrixLinear M).ker = 8 := by
  classical
  rw [Nat.card_eq_fintype_card]
  have he := Fintype.card_congr (activeVectorEquiv M)
  rw [Fintype.card_coe] at he
  rw [he]
  have hk : Fintype.card (binaryMatrixLinear M).ker =
      Fintype.card {x : E // binaryMatrixLinear M x = 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => LinearMap.mem_ker))
  rw [hk]
  rw [Fintype.card_subtype_compl]
  have hle := Fintype.card_subtype_le (fun x : E => binaryMatrixLinear M x = 0)
  have he := card_E
  omega

theorem binaryMatrix_active_sizes (M : BinaryMatrix) :
    (nonzeroMatrixBlocks M).card = 0 ∨ (nonzeroMatrixBlocks M).card = 4 ∨
    (nonzeroMatrixBlocks M).card = 6 ∨ (nonzeroMatrixBlocks M).card = 7 := by
  classical
  have hc := active_card_add_kernel M
  have hr := Submodule.finrank_le (binaryMatrixLinear M).ker
  have he : Module.finrank Bit E = 3 := by simp [E]
  rw [he] at hr
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := Bit)] at hc
  have hb : Fintype.card Bit = 2 := by rfl
  rw [hb] at hc
  interval_cases hk : Module.finrank Bit (binaryMatrixLinear M).ker <;> simp_all


theorem binaryMatrix_active_zero (M : BinaryMatrix) :
    (nonzeroMatrixBlocks M).card = 0 ↔ M = 0 := by
  constructor
  · intro h
    by_contra hm
    have := nonzeroMatrixBlocks_lower M hm
    omega
  · rintro rfl
    have hz (x : E) : matrixAt (0 : BinaryMatrix) x = 0 := by ext i; simp [matrixAt]
    simp [nonzeroMatrixBlocks,hz]

theorem binaryMatrix_active_seven (M : BinaryMatrix) :
    (nonzeroMatrixBlocks M).card = 7 ↔ IsUnit M := by
  classical
  rw [← Matrix.mulVec_injective_iff_isUnit]
  change _ ↔ Function.Injective (binaryMatrixLinear M)
  rw [← LinearMap.ker_eq_bot]
  constructor
  · intro h
    have hc := active_card_add_kernel M
    have hk : Nat.card (binaryMatrixLinear M).ker = 1 := by omega
    let : Subsingleton (binaryMatrixLinear M).ker := (Nat.card_eq_one_iff_unique.mp hk).1
    exact Submodule.eq_bot_of_subsingleton
  · intro h
    have hc := active_card_add_kernel M
    rw [h] at hc
    simp at hc
    omega

noncomputable def binarySevenEquiv :
    GL (Fin 3) Bit ≃ {M : BinaryMatrix // (nonzeroMatrixBlocks M).card = 7} where
  toFun u := ⟨u.val, (binaryMatrix_active_seven _).mpr u.isUnit⟩
  invFun M := ((binaryMatrix_active_seven M.val).mp M.prop).unit
  left_inv _u := Units.ext (IsUnit.unit_spec _)
  right_inv _M := Subtype.ext rfl

theorem binaryMatrix_seven_card :
    Nat.card {M : BinaryMatrix // (nonzeroMatrixBlocks M).card = 7} = 168 := by
  rw [← Nat.card_congr binarySevenEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ,ZMod.card]


theorem binaryMatrix_zero_card :
    Nat.card {M : BinaryMatrix // (nonzeroMatrixBlocks M).card = 0} = 1 := by
  classical
  have he := Equiv.subtypeEquivRight binaryMatrix_active_zero
  rw [Nat.card_congr he,Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_eq 0

theorem binaryMatrix_four_card :
    Nat.card {M : BinaryMatrix // (nonzeroMatrixBlocks M).card = 4} = 49 := by
  have hh (M : BinaryMatrix) : (nonzeroMatrixBlocks M).card = 4 ↔ isBinaryRankOne M := by
    rw [isBinaryRankOne_iff]
    constructor
    · intro h
      refine ⟨?_,h⟩
      intro hm
      have := (binaryMatrix_active_zero M).mpr hm
      omega
    · exact And.right
  rw [Nat.card_congr (Equiv.subtypeEquivRight hh)]
  exact binaryRankOne_card

theorem binaryMatrix_six_card :
    Nat.card {M : BinaryMatrix // (nonzeroMatrixBlocks M).card = 6} = 294 := by
  classical
  have hsum (M : BinaryMatrix) :
      (if (nonzeroMatrixBlocks M).card = 0 then 1 else 0) +
      (if (nonzeroMatrixBlocks M).card = 4 then 1 else 0) +
      (if (nonzeroMatrixBlocks M).card = 6 then 1 else 0) +
      (if (nonzeroMatrixBlocks M).card = 7 then 1 else 0) = (1 : ℕ) := by
    rcases binaryMatrix_active_sizes M with h|h|h|h <;> simp [h]
  have he := Finset.sum_congr (s₁ := (Finset.univ : Finset BinaryMatrix)) rfl (fun M _ => hsum M)
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one] at he
  have hcount (k : ℕ) :
      (Finset.univ.filter (fun M : BinaryMatrix => (nonzeroMatrixBlocks M).card = k)).card =
      Nat.card {M : BinaryMatrix // (nonzeroMatrixBlocks M).card = k} := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp only [hcount,binaryMatrix_zero_card,binaryMatrix_four_card,binaryMatrix_seven_card] at he
  have hall : Fintype.card BinaryMatrix = 512 := by
    change Fintype.card (Fin 3 → Fin 3 → ZMod 2) = 512
    norm_num [Fintype.card_fun,ZMod.card]
  norm_num [hall] at he
  rw [Nat.card_eq_fintype_card]
  omega

end Atlas.Rudvalis


