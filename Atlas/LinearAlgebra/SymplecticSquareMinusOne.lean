import Atlas.LinearAlgebra.SymplecticBasis
import Atlas.Algebra.FiniteFieldBinaryRepresentation
import Mathlib.Tactic

/-! # Normalized stable planes for symplectic square-minus-one operators -/
noncomputable section
namespace Atlas.AlternatingForm
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (B : LinearMap.BilinForm F V) (hA : B.IsAlt)
variable (t : V →ₗ[F] V) (ht : ∀ x, t (t x) = -x)
variable (hp : ∀ x y, B (t x) (t y) = B x y)

include hA ht hp in
/-- The form obtained by inserting t in the second slot is symmetric. -/
theorem squareMinusOne_twisted_symmetric (x y : V) : B x (t y) = B y (t x) := by
  calc
    B x (t y) = B (t x) (t (t y)) := (hp x (t y)).symm
    _ = -B (t x) y := by rw [ht,map_neg]
    _ = B y (t x) := hA.neg_eq (t x) y

include hA ht hp in
theorem squareMinusOne_nonzero_norm [Nontrivial V] (hB : B.Nondegenerate) (h2 : (2 : F) ≠ 0) :
    ∃ x : V, B x (t x) ≠ 0 := by
  by_contra! h
  have hz (x y : V) : B x (t y) = 0 := by
    have hh := h (x+y)
    simp only [map_add,LinearMap.add_apply] at hh
    have hs := squareMinusOne_twisted_symmetric B hA t ht hp y x
    have hx := h x
    have hy := h y
    apply mul_left_cancel₀ h2
    linear_combination hh - hx - hy - hs
  obtain ⟨x,hx⟩ := exists_ne (0 : V)
  apply hx
  apply hB.1 x
  intro y
  have hh := hz x (-t y)
  simpa only [map_neg,ht,neg_neg] using hh

include hA ht in
/-- The t-stable pair has the sum-of-two-squares norm formula. -/
theorem squareMinusOne_norm_combination (x : V) (r s : F) :
    B (r • x + s • t x) (t (r • x + s • t x)) =
      (r^2+s^2) * B x (t x) := by
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,ht,
    map_neg,smul_eq_mul,hA.self_eq_zero]
  rw [← hA.neg_eq x (t x)]
  ring

include hA ht hp in
/-- Every symplectic square-minus-one operator has a normalized stable pair over a finite odd field. -/
theorem squareMinusOne_exists_normalized [Finite F] [Nontrivial V]
    (hB : B.Nondegenerate) (h2 : (2 : F) ≠ 0) : ∃ x : V, B x (t x) = 1 := by
  obtain ⟨x,hx⟩ := squareMinusOne_nonzero_norm B hA t ht hp hB h2
  obtain ⟨r,s,hrs⟩ := Atlas.finite_field_sum_two_squares h2 (B x (t x))⁻¹
  refine ⟨r • x + s • t x,?_⟩
  rw [squareMinusOne_norm_combination B hA t ht,hrs,inv_mul_cancel₀ hx]

/-- The actual stable plane, defined as its span in the original module. -/
def squareMinusOnePlane (x : V) : Submodule F V := Submodule.span F {x,t x}

include ht in
theorem squareMinusOnePlane_stable (x y : V) (hy : y ∈ squareMinusOnePlane t x) :
    t y ∈ squareMinusOnePlane t x := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hy
  apply Submodule.mem_span_pair.mpr
  refine ⟨-b,a,?_⟩
  simp [map_add,map_smul,ht,neg_smul,smul_neg,add_comm]

variable (x : V) (hx : B x (t x) = 1)

include hA hx in
/-- Normalized coordinates on the actual plane, with ordered basis x,tx. -/
def squareMinusOnePlaneCoordinates : (F × F) ≃ₗ[F] squareMinusOnePlane t x where
  toFun z := ⟨z.1 • x + z.2 • t x,Submodule.mem_span_pair.mpr ⟨z.1,z.2,rfl⟩⟩
  invFun y := (B y.val (t x),-B y.val x)
  left_inv z := by
    ext <;> simp [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      hx,hA.self_eq_zero,← hA.neg_eq x (t x)]
  right_inv y := by
    apply Subtype.ext
    obtain ⟨a,b,hy⟩ := Submodule.mem_span_pair.mp y.prop
    change B y.val (t x) • x + (-B y.val x) • t x = y.val
    rw [← hy]
    simp [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      hx,hA.self_eq_zero,← hA.neg_eq x (t x)]
  map_add' a b := by
    apply Subtype.ext
    change (a.1+b.1) • x + (a.2+b.2) • t x = (a.1 • x+a.2 • t x)+(b.1 • x+b.2 • t x)
    module
  map_smul' c a := by
    apply Subtype.ext
    simp [smul_add,smul_smul]

include hA hx in
theorem squareMinusOnePlane_finrank : Module.finrank F (squareMinusOnePlane t x) = 2 := by
  have h := (squareMinusOnePlaneCoordinates B hA t x hx).finrank_eq
  simpa [Module.finrank_prod,Module.finrank_self] using h.symm

include hA hx in
theorem squareMinusOnePlane_nondegenerate : (B.restrict (squareMinusOnePlane t x)).Nondegenerate := by
  have hs : (B.restrict (squareMinusOnePlane t x)).SeparatingLeft := by
    intro y hy
    apply (squareMinusOnePlaneCoordinates B hA t x hx).symm.injective
    rw [map_zero]
    change (B y.val (t x),-B y.val x) = (0,0)
    have h1 := hy ⟨t x,Submodule.mem_span_pair.mpr ⟨0,1,by simp⟩⟩
    have h0 := hy ⟨x,Submodule.mem_span_pair.mpr ⟨1,0,by simp⟩⟩
    change B y.val (t x) = 0 at h1
    change B y.val x = 0 at h0
    simp [h1,h0]
  refine ⟨hs,?_⟩
  intro y hy
  apply hs y
  intro z
  change B y.val z.val = 0
  rw [← hA.neg_eq z.val y.val]
  change -((B.restrict (squareMinusOnePlane t x)) z y) = 0
  rw [hy z,neg_zero]

include hA ht hp hx in
/-- The existing orthogonal complement is stable too, so the plane can be split off inductively. -/
theorem squareMinusOne_complement_stable (y : V) (hy : y ∈ complement B x (t x)) :
    t y ∈ complement B x (t x) := by
  obtain ⟨h0,h1⟩ := hy
  change B y x = 0 at h0
  change B y (t x) = 0 at h1
  apply (mem_complement B x (t x) _).mpr
  constructor
  · have hh := hp y (t x)
    rw [ht,map_neg,h1] at hh
    exact neg_eq_zero.mp hh
  · rw [hp,h0]

include hA ht hp in
/-- A normalized, two-dimensional, nondegenerate invariant plane in the original symplectic module. -/
theorem squareMinusOne_stable_plane [Finite F] [Nontrivial V]
    (hB : B.Nondegenerate) (h2 : (2 : F) ≠ 0) :
    ∃ u : V, B u (t u) = 1 ∧ Module.finrank F (squareMinusOnePlane t u) = 2 ∧
      (B.restrict (squareMinusOnePlane t u)).Nondegenerate ∧
      (∀ y ∈ squareMinusOnePlane t u, t y ∈ squareMinusOnePlane t u) ∧
      (∀ y ∈ complement B u (t u), t y ∈ complement B u (t u)) := by
  obtain ⟨u,hu⟩ := squareMinusOne_exists_normalized B hA t ht hp hB h2
  exact ⟨u,hu,squareMinusOnePlane_finrank B hA t u hu,
    squareMinusOnePlane_nondegenerate B hA t u hu,
    squareMinusOnePlane_stable t ht u,
    squareMinusOne_complement_stable B hA t ht hp u hu⟩

end Atlas.AlternatingForm


