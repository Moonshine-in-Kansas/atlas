import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
namespace Atlas.Combinatorics
open scoped BigOperators

def fiberLabels {X I : Type*} [Fintype I] (f : X → I) (S : Set X) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ x ∈ S, f x = i)

theorem mem_fiberLabels {X I : Type*} [Fintype I] (f : X → I) (S : Set X)
    (hs : ∀ x ∈ S, ∀ y, f x = f y → y ∈ S) (y : X) :
    f y ∈ fiberLabels f S ↔ y ∈ S := by
  classical
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := (Finset.mem_filter.mp h).2
    exact hs x hx y he
  · intro hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hy,rfl⟩

theorem saturated_set_card {X I : Type*} [Finite X] [Fintype I] (f : X → I)
    (d : I → ℕ) (hd : ∀ i, Nat.card {x : X // f x = i} = d i)
    (S : Set X) (hs : ∀ x ∈ S, ∀ y, f x = f y → y ∈ S) :
    Nat.card S = ∑ i ∈ fiberLabels f S, d i := by
  classical
  have hf (i : I) : Nat.card {x : S // f x.val = i} = if i ∈ fiberLabels f S then d i else 0 := by
    split_ifs with hi
    · have hmem (y : X) (hy : f y = i) : y ∈ S :=
        (mem_fiberLabels f S hs y).mp (hy.symm ▸ hi)
      let e : {x : S // f x.val = i} ≃ {x : X // f x = i} :=
        { toFun := fun x => ⟨x.val.val,x.prop⟩
          invFun := fun x => ⟨⟨x.val,hmem x.val x.prop⟩,x.prop⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact (Nat.card_congr e).trans (hd i)
    · letI : IsEmpty {x : S // f x.val = i} := ⟨fun x => hi
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x.val.val,x.val.prop,x.prop⟩)⟩
      simp
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fun x : S => f x.val)),Nat.card_sigma]
  simp_rw [hf]
  simp only [fiberLabels,Finset.mem_filter,Finset.mem_univ,true_and,Finset.sum_filter]

end Atlas.Combinatorics
