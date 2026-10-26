import Atlas.Rudvalis.QuadraticMinimumPattern
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Symbolic fibre counts for the transpose contraction controlling quadratic weights. -/
namespace Atlas.Rudvalis
open scoped BigOperators

def transposeContraction (c : E) : BinaryMatrix →ₗ[Bit] E where
  toFun M := matrixAt M.transpose c
  map_add' A B := by ext j; simp [matrixAt,add_mul,Finset.sum_add_distrib]
  map_smul' a A := by ext j; simp [matrixAt,Finset.mul_sum,mul_assoc]

theorem transposeContraction_surjective (c : E) (hc : c ≠ 0) :
    Function.Surjective (transposeContraction c) := by
  obtain ⟨i,hi⟩ := point_has_one (⟨c,hc⟩ : Point)
  change c i = 1 at hi
  intro b
  refine ⟨(columnMatrix i b).transpose, ?_⟩
  change matrixAt (columnMatrix i b) c = b
  rw [matrixAt_column,hi,one_smul]

theorem transposeContraction_ker_finrank (c : E) (hc : c ≠ 0) :
    Module.finrank Bit (transposeContraction c).ker = 6 := by
  have h := LinearMap.finrank_range_add_finrank_ker (transposeContraction c)
  rw [LinearMap.range_eq_top.mpr (transposeContraction_surjective c hc)] at h
  have he : Module.finrank Bit E = 3 := by simp [E,Module.finrank_pi_fintype]
  have hm : Module.finrank Bit BinaryMatrix = 9 := by
    change Module.finrank Bit (Fin 3 → Fin 3 → Bit) = 9
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_pi_fintype]
  simp only [finrank_top,he,hm] at h
  omega

theorem transposeContraction_ker_card (c : E) (hc : c ≠ 0) :
    Nat.card (transposeContraction c).ker = 64 := by
  classical
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := Bit),
    transposeContraction_ker_finrank c hc]
  rfl

noncomputable def transposeContractionFibreEquiv (c : E) (hc : c ≠ 0) (b : E) :
    (transposeContraction c).ker ≃ {M : BinaryMatrix // transposeContraction c M = b} := by
  let A := (transposeContraction_surjective c hc b).choose
  have hA : transposeContraction c A = b := (transposeContraction_surjective c hc b).choose_spec
  exact {
    toFun := fun M => ⟨M.val+A, by rw [map_add,LinearMap.mem_ker.mp M.prop,hA,zero_add]⟩
    invFun := fun M => ⟨M.val-A, by rw [LinearMap.mem_ker,map_sub,M.prop,hA,sub_self]⟩
    left_inv := fun M => by apply Subtype.ext; simp
    right_inv := fun M => by apply Subtype.ext; simp }

theorem transposeContraction_fibre_card (c : E) (hc : c ≠ 0) (b : E) :
    Nat.card {M : BinaryMatrix // matrixAt M.transpose c = b} = 64 := by
  change Nat.card {M : BinaryMatrix // transposeContraction c M = b} = 64
  rw [← Nat.card_congr (transposeContractionFibreEquiv c hc b)]
  exact transposeContraction_ker_card c hc

end Atlas.Rudvalis
