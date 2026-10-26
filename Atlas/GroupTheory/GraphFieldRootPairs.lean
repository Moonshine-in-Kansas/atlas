import Atlas.GroupTheory.GraphFieldFixedPoints
import Mathlib.Algebra.Group.Commute.Defs

/-! Fixed root parameters for a pair of commuting root subgroups exchanged
by a graph--field involution. The actual root embeddings, their commutation,
and their independent parameters are explicit application obligations. -/
namespace Atlas.GroupTheory
variable {G A : Type*} [Group G] [Group A]

def exchangedRootPairHom (a : G ≃* G) (field : A ≃* A)
    (hf : Function.Involutive field) (x y : A →* G)
    (hx : ∀ t, a (x t) = y (field t))
    (hy : ∀ t, a (y t) = x (field t))
    (hc : ∀ s t, Commute (x s) (y t)) :
    A →* automorphismFixedSubgroup a where
  toFun t := ⟨x t * y (field t), by
    change a (x t * y (field t)) = x t * y (field t)
    rw [map_mul, hx, hy, hf]
    exact (hc t (field t)).eq.symm⟩
  map_one' := Subtype.ext (by simp only [map_one, mul_one]; rfl)
  map_mul' s t := Subtype.ext (by
    simp only [map_mul]
    exact (hc t (field s)).mul_mul_mul_comm (x s) (y (field t)))

@[simp] theorem exchangedRootPairHom_val (a : G ≃* G) (field : A ≃* A)
    (hf : Function.Involutive field) (x y : A →* G)
    (hx : ∀ t, a (x t) = y (field t))
    (hy : ∀ t, a (y t) = x (field t))
    (hc : ∀ s t, Commute (x s) (y t)) (t : A) :
    (exchangedRootPairHom a field hf x y hx hy hc t).val = x t * y (field t) := rfl

theorem exchangedRootPairHom_injective (a : G ≃* G) (field : A ≃* A)
    (hf : Function.Involutive field) (x y : A →* G)
    (hx : ∀ t, a (x t) = y (field t))
    (hy : ∀ t, a (y t) = x (field t))
    (hc : ∀ s t, Commute (x s) (y t))
    (hind : Function.Injective (fun p : A × A => x p.1 * y p.2)) :
    Function.Injective (exchangedRootPairHom a field hf x y hx hy hc) := by
  intro s t h
  have hp : (s, field s) = (t, field t) := hind (congrArg Subtype.val h)
  exact congrArg Prod.fst hp

end Atlas.GroupTheory
