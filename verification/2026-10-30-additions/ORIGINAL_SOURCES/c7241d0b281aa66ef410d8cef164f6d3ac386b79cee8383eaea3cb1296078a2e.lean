import FamilyWork.PositiveOrbitOrder
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Product equivariance for the explicit positive-root orbit blocks. The
ambient group need not be commutative: only the two roots in a moved orbit
are required to commute. No group normal form is assumed or concluded here. -/

namespace Atlas.Chevalley.TwistedE6

variable {G K : Type*} [Monoid G]
  (x : Fin 36 → K → G) (θ : G →* G) (bar : K → K)
  (htwist : ∀ i t, θ (x i t) = x (positiveDiagram i) (bar t))
  (hcomm : ∀ i, positiveDiagram i ≠ i → ∀ s t,
    Commute (x i s) (x (positiveDiagram i) t))

/-- The literal ordered word; no commutativity between different blocks. -/
def positiveOrbitProduct (s : Fin 36 → K) : G :=
  (e6PositiveOrbitOrder.map fun i => x i (s i)).prod

include htwist hcomm

theorem positiveOrbitBlock_twist (s : Fin 36 → K) (i : Fin 36) :
    θ ((e6PositiveOrbitBlock i).map fun j => x j (s j)).prod =
      ((e6PositiveOrbitBlock i).map fun j => x j (bar (s (positiveDiagram j)))).prod := by
  by_cases hi : positiveDiagram i = i
  · simp only [e6PositiveOrbitBlock_of_fixed i hi, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, htwist, hi]
  · simp only [e6PositiveOrbitBlock_of_moved i hi, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, map_mul, htwist,
      positiveDiagram_involutive i]
    exact (hcomm i hi (bar (s (positiveDiagram i))) (bar (s i))).eq.symm

theorem positiveOrbitBlocks_twist (s : Fin 36 → K) (l : List (Fin 36)) :
    θ ((l.flatMap e6PositiveOrbitBlock).map fun i => x i (s i)).prod =
      ((l.flatMap e6PositiveOrbitBlock).map fun i =>
        x i (bar (s (positiveDiagram i)))).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append, map_mul]
    rw [positiveOrbitBlock_twist x θ bar htwist hcomm s i, ih]

theorem positiveOrbitProduct_twist (s : Fin 36 → K) :
    θ (positiveOrbitProduct x s) =
      positiveOrbitProduct x (fun i => bar (s (positiveDiagram i))) := by
  unfold positiveOrbitProduct
  rw [e6PositiveOrbitOrder_eq_flatMap]
  exact positiveOrbitBlocks_twist x θ bar htwist hcomm s e6PositiveOrbitRepresentatives

/-- Uniqueness of coordinates turns the group fixed-point equation into the
literal orbit equations. No assumption about the order of the group is used. -/
theorem positiveOrbitProduct_fixed_iff
    (hinj : Function.Injective (positiveOrbitProduct x))
    (hbar : Function.Involutive bar) (s : Fin 36 → K) :
    θ (positiveOrbitProduct x s) = positiveOrbitProduct x s ↔
      ∀ i, s (positiveDiagram i) = bar (s i) := by
  constructor
  · intro h i
    have hp := hinj ((positiveOrbitProduct_twist x θ bar htwist hcomm s).symm.trans h)
    have hi := congrFun hp (positiveDiagram i)
    simpa only [positiveDiagram_involutive i] using hi.symm
  · intro h
    rw [positiveOrbitProduct_twist x θ bar htwist hcomm]
    congr 1
    funext i
    rw [h i, hbar (s i)]

end Atlas.Chevalley.TwistedE6
