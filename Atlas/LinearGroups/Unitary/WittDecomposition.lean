import Atlas.LinearGroups.Unitary.WittPair
import Mathlib.LinearAlgebra.Pi

/-! Actual Witt-coordinate equivalences in all even and odd dimensions.
Every two-dimensional block uses the proved characteristic-uniform plane isometry;
an odd-dimensional space retains one anisotropic coordinate of norm one. -/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Orthogonal sum of the displayed hyperbolic pairs. -/
def hyperbolicSumForm {r : ℕ} (x y : Fin r → Fin 2 → K) : K :=
  ∑ i, hyperbolicPlaneForm (F := F) (x i) (y i)

/-- Apply the actual plane equivalence on every block and flatten the coordinates. -/
def evenWittEquiv (r : ℕ) (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
    (Fin r → Fin 2 → K) ≃ₗ[K] (Fin (r * 2) → K) where
  toFun x k := e (x (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2
  invFun y i := e.symm (fun j => y (finProdFinEquiv (i,j)))
  left_inv x := by
    funext i
    simp
  right_inv y := by
    funext k
    have h := congrFun (e.apply_symm_apply (fun j =>
      y (finProdFinEquiv ((finProdFinEquiv.symm k).1, j))))
      (finProdFinEquiv.symm k).2
    exact h.trans (congrArg y (finProdFinEquiv.apply_symm_apply k))
  map_add' x y := by funext k; simp
  map_smul' a x := by funext k; simp

theorem evenWittEquiv_preserves (r : ℕ)
    (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
    (he : ∀ x y, hermitian F K (e x) (e y) = hyperbolicPlaneForm (F := F) x y)
    (x y : Fin r → Fin 2 → K) :
    hermitian F K (evenWittEquiv r e x) (evenWittEquiv r e y) =
      hyperbolicSumForm (F := F) x y := by
  change (∑ k : Fin (r * 2), _) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin r × Fin 2 ≃ Fin (r * 2))]
  simp only [evenWittEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Equiv.symm_apply_apply, Fintype.sum_prod_type]
  change (∑ i, hermitian F K (e (x i)) (e (y i))) = _
  simp only [he, hyperbolicSumForm]

/-- Every even-dimensional standard space is an actual sum of hyperbolic planes. -/
theorem exists_evenWittEquiv (hdeg : Module.finrank F K = 2) (r : ℕ) :
    ∃ e : (Fin r → Fin 2 → K) ≃ₗ[K] (Fin (r * 2) → K),
      ∀ x y, hermitian F K (e x) (e y) = hyperbolicSumForm (F := F) x y := by
  obtain ⟨e, he⟩ := exists_wittPlaneEquiv hdeg
  exact ⟨evenWittEquiv r e, evenWittEquiv_preserves r e he⟩

/-- Add the actual norm-one anisotropic coordinate in odd dimension. -/
def oddWittEquiv (r : ℕ) (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :
    (K × (Fin r → Fin 2 → K)) ≃ₗ[K] (Fin (r * 2 + 1) → K) where
  toFun x := Fin.cons x.1 (evenWittEquiv r e x.2)
  invFun y := (y 0, (evenWittEquiv r e).symm (Fin.tail y))
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem oddWittEquiv_preserves (r : ℕ)
    (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
    (he : ∀ x y, hermitian F K (e x) (e y) = hyperbolicPlaneForm (F := F) x y)
    (x y : K × (Fin r → Fin 2 → K)) :
    hermitian F K (oddWittEquiv r e x) (oddWittEquiv r e y) =
      x.1 * conjugation F K y.1 + hyperbolicSumForm (F := F) x.2 y.2 := by
  change hermitian F K (Fin.cons x.1 _) (Fin.cons y.1 _) = _
  simp only [hermitian, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [show (∑ i, evenWittEquiv r e x.2 i * conjugation F K (evenWittEquiv r e y.2 i)) =
      hyperbolicSumForm (F := F) x.2 y.2 from evenWittEquiv_preserves r e he x.2 y.2]

/-- Every odd-dimensional standard space is the actual orthogonal sum of a
norm-one anisotropic line and the indicated hyperbolic pairs. -/
theorem exists_oddWittEquiv (hdeg : Module.finrank F K = 2) (r : ℕ) :
    ∃ e : (K × (Fin r → Fin 2 → K)) ≃ₗ[K] (Fin (r * 2 + 1) → K),
      ∀ x y, hermitian F K (e x) (e y) =
        x.1 * conjugation F K y.1 + hyperbolicSumForm (F := F) x.2 y.2 := by
  obtain ⟨e, he⟩ := exists_wittPlaneEquiv hdeg
  exact ⟨oddWittEquiv r e, oddWittEquiv_preserves r e he⟩
end Atlas.Unitary
