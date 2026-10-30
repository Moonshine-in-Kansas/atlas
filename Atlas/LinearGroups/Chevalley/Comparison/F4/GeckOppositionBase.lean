import Atlas.LinearGroups.Chevalley.Comparison.F4.GeckOperatorsBase

/-! Actual opposition and lowering parameters in the same marked 52-space.
-/
noncomputable section
namespace Atlas.Chevalley.Comparison.F4
open Integral F4Data
open scoped Matrix
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def opposite52 : Fin 52 → Fin 52 :=
  ![0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12,19,18,17,16,23,22,21,20,27,26,25,24,29,28,31,30,33,32,35,34,51,50,49,48,47,46,45,44,43,42,41,40,39,38,37,36]

theorem opposite52_involutive : Function.Involutive opposite52 := by
  intro a
  fin_cases a <;> rfl

variable (R : Type*) [CommRing R]
def opposition52 : Matrix (Fin 52) (Fin 52) R :=
  fun a c => if a=opposite52 c then 1 else 0

private theorem left_opposition52 (A : Matrix (Fin 52) (Fin 52) R) (a c : Fin 52) :
    (opposition52 R * A) a c = A (opposite52 a) c := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (opposite52 a)]
  · simp only [opposition52, opposite52_involutive a, ite_true, one_mul]
  · intro j _ hj
    have h : a ≠ opposite52 j := by
      intro he
      apply hj
      exact (opposite52_involutive j).symm.trans (congrArg opposite52 he.symm)
    simp [opposition52, h]
  · simp

private theorem right_opposition52 (A : Matrix (Fin 52) (Fin 52) R) (a c : Fin 52) :
    (A * opposition52 R) a c = A a (opposite52 c) := by
  rw [Matrix.mul_apply]
  simp [opposition52]

theorem opposition52_conjugation (A : Matrix (Fin 52) (Fin 52) R) (a c : Fin 52) :
    (opposition52 R * A * opposition52 R) a c = A (opposite52 a) (opposite52 c) := by
  rw [right_opposition52, left_opposition52]

/-- The literal numeric opposition fixes the Cartan coordinates and negates
the existing root labels. Only the 52 labels are reduced here. -/
theorem opposite52_finSumFinEquiv (x : I) :
    opposite52 ((finSumFinEquiv : I ≃ Fin 52) x) =
      (finSumFinEquiv : I ≃ Fin 52) (Sum.map id opposite x) := by
  rcases x with a | j
  · fin_cases a <;> rfl
  · fin_cases j <;> rfl

/-- Four symbolic block cases, uniformly over the coefficient ring. -/
private theorem W_sum_permutation (a c : I) :
    W R a c = if a = Sum.map id opposite c then 1 else 0 := by
  rcases a with a | a <;> rcases c with c | c <;>
    simp [W, Matrix.fromBlocks, Matrix.one_apply]

private theorem W_numeric_table (a c : Fin 52) :
    W R ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm a)
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c) = opposition52 R a c := by
  obtain ⟨x, rfl⟩ := (finSumFinEquiv : I ≃ Fin 52).surjective a
  obtain ⟨y, rfl⟩ := (finSumFinEquiv : I ≃ Fin 52).surjective c
  simp only [Equiv.symm_apply_apply, W_sum_permutation, opposition52,
    opposite52_finSumFinEquiv, (finSumFinEquiv : I ≃ Fin 52).injective.eq_iff]

theorem reindex52_opposition :
    reindex52 R (oppositionOver pairing base R) = opposition52 R := by
  ext a c
  have h := congrArg (fun M : Matrix I I R =>
    M ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm a)
      ((finSumFinEquiv : Fin 4 ⊕ Fin 48 ≃ Fin 52).symm c)) (reindex_opposition R)
  exact h.trans (W_numeric_table R a c)

end Atlas.Chevalley.Comparison.F4
