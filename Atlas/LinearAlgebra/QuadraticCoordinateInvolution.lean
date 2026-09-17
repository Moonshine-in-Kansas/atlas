import Atlas.LinearAlgebra.QuadraticDiagonalNormalization
import Atlas.LinearAlgebra.InvolutionEigenspaces
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
namespace Atlas.Quadratic
variable {F : Type*} [Field F]

def coordinateSign (N k : ℕ) : (Fin N → F) ≃ₗ[F] (Fin N → F) where
  toFun x i := if i.val < k then -x i else x i
  invFun x i := if i.val < k then -x i else x i
  left_inv x := by ext i; dsimp; split <;> simp
  right_inv x := by ext i; dsimp; split <;> simp
  map_add' x y := by ext i; dsimp; split <;> simp [add_comm]
  map_smul' c x := by ext i; dsimp; split <;> simp

@[simp] theorem coordinateSign_apply (N k : ℕ) (x : Fin N → F) (i : Fin N) :
    coordinateSign N k x i = if i.val < k then -x i else x i := rfl

theorem coordinateSign_involutive (N k : ℕ) : Function.Involutive (coordinateSign (F := F) N k) := by
  intro x
  ext i
  simp only [coordinateSign_apply]
  split <;> simp_all

def coordinateSignIsometry {N : ℕ} (w : Fin N → F) (k : ℕ) :
    (diagonalForm w).IsometryEquiv (diagonalForm w) where
  toLinearEquiv := coordinateSign N k
  map_app' x := by
    simp only [diagonalForm,QuadraticMap.weightedSumSquares_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    change w i * ((if i.val < k then -x i else x i) * (if i.val < k then -x i else x i)) = w i * (x i * x i)
    split <;> ring

def coordinateSignMinusEquiv (N k : ℕ) (hk : k ≤ N) (h2 : (2 : F) ≠ 0) :
    (Fin k → F) ≃ₗ[F] Atlas.LinearInvolution.minus (coordinateSign (F := F) N k).toLinearMap where
  toFun x := ⟨fun i => if hi : i.val < k then x ⟨i.val,hi⟩ else 0, by
    rw [Atlas.LinearInvolution.mem_minus]
    ext i
    simp only [LinearEquiv.coe_coe,coordinateSign_apply,Pi.neg_apply]
    split <;> simp_all⟩
  invFun x i := x.val ⟨i.val,lt_of_lt_of_le i.isLt hk⟩
  left_inv x := by ext i; simp [i.isLt]
  right_inv x := by
    apply Subtype.ext
    ext i
    dsimp only
    by_cases hi : i.val < k
    · simp [hi]
    · simp only [dif_neg hi]
      have hx := congrFun ((Atlas.LinearInvolution.mem_minus _ _).mp x.prop) i
      change (if i.val < k then -x.val i else x.val i) = -x.val i at hx
      rw [if_neg hi] at hx
      have hz : (2 : F) * x.val i = 0 := by linear_combination hx
      exact ((mul_eq_zero.mp hz).resolve_left h2).symm
  map_add' x y := by apply Subtype.ext; ext i; dsimp; split <;> simp
  map_smul' c x := by apply Subtype.ext; ext i; dsimp; split <;> simp

theorem coordinateSign_finrank_minus (N k : ℕ) (hk : k ≤ N) (h2 : (2 : F) ≠ 0) :
    Module.finrank F (Atlas.LinearInvolution.minus (coordinateSign (F := F) N k).toLinearMap) = k := by
  rw [← (coordinateSignMinusEquiv N k hk h2).finrank_eq,Module.finrank_fin_fun]


/-- The selected coordinate minus space carries exactly the sum-of-squares form. -/
def coordinateSignMinusIsometry {N : ℕ} (w : Fin N → F) (k : ℕ)
    (hk : k ≤ N) (h2 : (2 : F) ≠ 0) (hw : ∀ i : Fin N, i.val < k → w i = 1) :
    (diagonalForm (fun _ : Fin k => (1 : F))).IsometryEquiv
      ((diagonalForm w).comp (Atlas.LinearInvolution.minus
        (coordinateSign (F := F) N k).toLinearMap).subtype) where
  toLinearEquiv := coordinateSignMinusEquiv N k hk h2
  map_app' x := by
    change (diagonalForm w) (fun i => if hi : i.val < k then x ⟨i.val,hi⟩ else 0) = _
    simp only [diagonalForm,QuadraticMap.weightedSumSquares_apply,smul_eq_mul,one_mul]
    symm
    apply Finset.sum_bij_ne_zero (fun (i : Fin k) _ _ => (⟨i.val,lt_of_lt_of_le i.isLt hk⟩ : Fin N))
    · intros; exact Finset.mem_univ _
    · intro i hi hni j hj hnj he
      exact Fin.ext (congrArg (fun z : Fin N => z.val) he)
    · intro j hj hnj
      have hlt : j.val < k := by
        by_contra hn
        simp [hn] at hnj
      refine ⟨⟨j.val,hlt⟩,Finset.mem_univ _,?_,?_⟩
      · simpa only [dif_pos hlt,hw j hlt,one_mul] using hnj
      · exact Fin.ext rfl
    · intro i hi hni
      simp [i.isLt,hw (⟨i.val,lt_of_lt_of_le i.isLt hk⟩ : Fin N) i.isLt]
end Atlas.Quadratic
