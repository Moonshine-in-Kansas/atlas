import Atlas.LinearGroups.Chevalley.TorusConjugation
import Mathlib.Data.Finset.NoncommProd

/-! Actual torus parameter homomorphisms and their matrix-level kernel.
No claim about expected torus size or group center is made here. -/
noncomputable section
namespace Atlas.Chevalley
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (R : Type*) [CommRing R]

def adjointTorusHom (i : b.support) : Rˣ →* Adjoint P b R where
  toFun := adjointTorus P b R i
  map_one' := by simp [adjointTorus]
  map_mul' := adjointTorus_mul P b R i

@[simp] theorem adjointTorusHom_apply (i : b.support) (t : Rˣ) :
    adjointTorusHom P b R i t = adjointTorus P b R i t := rfl

/-- Exact root-weight kernel, expressed in the scalar unit group. -/
theorem adjointTorusHom_eq_one_iff (i : b.support) (t : Rˣ) :
    adjointTorusHom P b R i t = 1 ↔ ∀ j : ι, t ^ P.pairingIn ℤ j i = 1 := by
  constructor
  · intro h j
    have hm := congrArg (fun g : Adjoint P b R => g.val.val) h
    change (adjointTorus P b R i t).val.val = 1 at hm
    rw [adjointTorus_matrix] at hm
    have hj := congrArg (fun A => A (Sum.inr j) (Sum.inr j)) hm
    apply Units.ext
    simpa [adjointTorusCoordinate] using hj
  · intro h
    apply Subtype.ext
    apply Units.ext
    change (adjointTorus P b R i t).val.val = 1
    rw [adjointTorus_matrix]
    have hw : adjointTorusCoordinate P b R i t = fun _ => 1 := by
      funext a
      cases a <;> simp [adjointTorusCoordinate, h]
    rw [hw, Matrix.diagonal_one]

/-- Finite products in the actual noncommutative group are formed only with
an explicit proof that all the chosen factors commute. -/
def adjointTorusProduct (s : Finset b.support) (t : b.support → Rˣ) : Adjoint P b R :=
  s.noncommProd (fun i => adjointTorus P b R i (t i))
    (fun i _ j _ _ => adjointTorus_commute P b R i j (t i) (t j))

set_option backward.isDefEq.respectTransparency false in
/-- All simple-coroot parameters, mapped into the actual generated group. -/
def adjointTorusParameters : (b.support → Rˣ) →* Adjoint P b R where
  toFun t := adjointTorusProduct P b R Finset.univ t
  map_one' := by
    unfold adjointTorusProduct
    rw [Finset.noncommProd_eq_pow_card _ _ _ 1]
    · simp
    · intro i hi
      simp [adjointTorus]
  map_mul' t u := by
    unfold adjointTorusProduct
    simp only [Pi.mul_apply, adjointTorus_mul]
    exact Finset.noncommProd_mul_distrib
      (fun i => adjointTorus P b R i (t i))
      (fun i => adjointTorus P b R i (u i))
      (fun i _ j _ _ => adjointTorus_commute P b R i j (t i) (t j))
      (fun i _ j _ _ => adjointTorus_commute P b R i j (u i) (u j))
      (fun i _ j _ _ => adjointTorus_commute P b R i j (u i) (t j))

set_option backward.isDefEq.respectTransparency false in
/-- Literal coordinate product: scalar roots see the product of their weights. -/
theorem adjointTorusProduct_matrix (s : Finset b.support) (t : b.support → Rˣ) :
    (adjointTorusProduct P b R s t).val.val =
      Matrix.diagonal (fun a => ∏ i ∈ s, adjointTorusCoordinate P b R i (t i) a) := by
  induction s using Finset.induction_on with
  | empty => simp [adjointTorusProduct]
  | @insert i s hi ih =>
    unfold adjointTorusProduct at *
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]
    change (adjointTorus P b R i (t i)).val.val * _ = _
    rw [adjointTorus_matrix, ih, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    simp only [Finset.prod_insert hi]

/-- Exact tuple kernel; no quotient-cardinality or center formula is assumed. -/
theorem adjointTorusParameters_eq_one_iff (t : b.support → Rˣ) :
    adjointTorusParameters P b R t = 1 ↔
      ∀ j : ι, ∏ i : b.support, (t i) ^ P.pairingIn ℤ j i = 1 := by
  constructor
  · intro h j
    have hm := congrArg (fun g : Adjoint P b R => g.val.val) h
    change (adjointTorusProduct P b R Finset.univ t).val.val = 1 at hm
    rw [adjointTorusProduct_matrix] at hm
    have hj := congrArg (fun A => A (Sum.inr j) (Sum.inr j)) hm
    apply Units.ext
    simpa [adjointTorusCoordinate, map_prod] using hj
  · intro h
    apply Subtype.ext
    apply Units.ext
    change (adjointTorusProduct P b R Finset.univ t).val.val = 1
    rw [adjointTorusProduct_matrix]
    have hw : (fun a => ∏ i : b.support, adjointTorusCoordinate P b R i (t i) a) =
        fun _ => 1 := by
      funext a
      cases a with
      | inl j => simp [adjointTorusCoordinate]
      | inr j =>
        have hj := congrArg Units.val (h j)
        simpa [adjointTorusCoordinate, map_prod] using hj
    rw [hw, Matrix.diagonal_one]

end Atlas.Chevalley
