import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-! Uniform signs on the Boolean spin basis; no division by two. -/
namespace Atlas.BooleanSpin
open scoped BigOperators
variable {I : Type*} [Fintype I] [LinearOrder I]
variable (R : Type*) [CommRing R]

def bitSign (b : Bool) : R := if b then -1 else 1

def flip (i : I) (σ : I → Bool) : I → Bool := Function.update σ i (!(σ i))

@[simp] theorem flip_self (i : I) (σ : I → Bool) : flip i σ i = !(σ i) := by
  simp [flip]

@[simp] theorem flip_of_ne (i j : I) (hji : j ≠ i) (σ : I → Bool) :
    flip i σ j = σ j := by simp [flip, hji]

@[simp] theorem flip_flip (i : I) (σ : I → Bool) : flip i (flip i σ) = σ := by
  funext j
  by_cases h : j=i
  · subst j; simp
  · simp [flip_of_ne, h]

theorem flip_comm (i j : I) (hij : i ≠ j) (σ : I → Bool) :
    flip i (flip j σ) = flip j (flip i σ) := by
  simp only [flip, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
  exact Function.update_comm (Ne.symm hij) _ _ _

@[simp] theorem bitSign_not (b : Bool) : bitSign R (!b) = -bitSign R b := by
  cases b <;> simp [bitSign]

@[simp] theorem bitSign_mul_self (b : Bool) : bitSign R b * bitSign R b = 1 := by
  cases b <;> simp [bitSign]

def signProduct (s : Finset I) (σ : I → Bool) : R := ∏ j ∈ s, bitSign R (σ j)

theorem signProduct_mul_self (s : Finset I) (σ : I → Bool) :
    signProduct R s σ * signProduct R s σ = 1 := by
  simp only [signProduct, ← Finset.prod_mul_distrib, bitSign_mul_self, Finset.prod_const_one]

theorem signProduct_flip (s : Finset I) (i : I) (σ : I → Bool) :
    signProduct R s (flip i σ) = if i ∈ s then -signProduct R s σ else signProduct R s σ := by
  by_cases hi : i ∈ s
  · simp only [if_pos hi, signProduct]
    rw [← Finset.mul_prod_erase s (fun j => bitSign R (flip i σ j)) hi,
      ← Finset.mul_prod_erase s (fun j => bitSign R (σ j)) hi]
    have hp : (∏ j ∈ s.erase i, bitSign R (flip i σ j)) =
        ∏ j ∈ s.erase i, bitSign R (σ j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [flip_of_ne i j (Finset.mem_erase.mp hj).1]
    rw [flip_self, bitSign_not, hp, neg_mul]
  · simp only [if_neg hi, signProduct]
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (bitSign R) (flip_of_ne i j (by intro h; subst j; exact hi hj) σ)

def «prefix» (i : I) (σ : I → Bool) : R :=
  signProduct R (Finset.univ.filter (fun j => j < i)) σ

def paritySign (σ : I → Bool) : R := signProduct R Finset.univ σ

theorem prefix_mul_self (i : I) (σ : I → Bool) : «prefix» R i σ * «prefix» R i σ = 1 :=
  signProduct_mul_self R _ σ

theorem paritySign_mul_self (σ : I → Bool) : paritySign R σ * paritySign R σ = 1 :=
  signProduct_mul_self R _ σ

theorem prefix_flip (i j : I) (σ : I → Bool) :
    «prefix» R i (flip j σ) = if j < i then -«prefix» R i σ else «prefix» R i σ := by
  simp [«prefix», signProduct_flip]

@[simp] theorem prefix_flip_self (i : I) (σ : I → Bool) : «prefix» R i (flip i σ) = «prefix» R i σ := by
  simp [prefix_flip]

@[simp] theorem paritySign_flip (i : I) (σ : I → Bool) :
    paritySign R (flip i σ) = -paritySign R σ := by
  simp [paritySign, signProduct_flip]

theorem prefix_adjacent (n : ℕ) (i : Fin n) (σ : Fin (n+1) → Bool) :
    «prefix» R i.succ σ = bitSign R (σ i.castSucc) * «prefix» R i.castSucc σ := by
  have hs : Finset.univ.filter (fun j : Fin (n+1) => j < i.succ) =
      insert i.castSucc (Finset.univ.filter (fun j => j < i.castSucc)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
    omega
  have hn : i.castSucc ∉ Finset.univ.filter (fun j : Fin (n+1) => j < i.castSucc) := by simp
  simp only [«prefix», hs, signProduct, Finset.prod_insert hn]

theorem paritySign_last (n : ℕ) (σ : Fin (n+1) → Bool) :
    paritySign R σ = bitSign R (σ (Fin.last n)) * «prefix» R (Fin.last n) σ := by
  have hs : (Finset.univ : Finset (Fin (n+1))) =
      insert (Fin.last n) (Finset.univ.filter (fun j => j < Fin.last n)) := by
    ext j
    simp [Fin.lt_last_iff_ne_last]
    exact em (j = Fin.last n)
  have hn : Fin.last n ∉ Finset.univ.filter (fun j : Fin (n+1) => j < Fin.last n) := by simp
  unfold paritySign
  rw [hs]
  simp only [signProduct, Finset.prod_insert hn, «prefix»]

end Atlas.BooleanSpin
