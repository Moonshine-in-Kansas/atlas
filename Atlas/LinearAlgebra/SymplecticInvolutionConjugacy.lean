import Atlas.LinearAlgebra.AlternatingFormIsometry
import Atlas.LinearAlgebra.InvolutionConjugacy

/-! # Actual symplectic involution conjugacy from minus-eigenspace dimension -/
noncomputable section


namespace Atlas.AlternatingForm
universe u v w
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {W : Type w} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
open Atlas.LinearInvolution

/-- The minus-eigenspace dimension determines a symplectic involution up to actual isometry. -/
theorem involution_isometry_exists (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate)
    (C : LinearMap.BilinForm F W) (hCalt : C.IsAlt) (hC : C.Nondegenerate)
    (t : V →ₗ[F] V) (s : W →ₗ[F] W) (ht : Function.Involutive t) (hs : Function.Involutive s)
    (hp : ∀ x y, B (t x) (t y) = B x y) (hsp : ∀ x y, C (s x) (s y) = C x y)
    (h2 : (2 : F) ≠ 0) (hdim : Module.finrank F V = Module.finrank F W)
    (hm : Module.finrank F (minus t) = Module.finrank F (minus s)) :
    ∃ e : V ≃ₗ[F] W, (∀ x y, C (e x) (e y) = B x y) ∧ (∀ x, e (t x) = s (e x)) := by
  have hpd : Module.finrank F (plus t) = Module.finrank F (plus s) := by
    have h1 := finrank_plus_add_minus t ht h2
    have h2' := finrank_plus_add_minus s hs h2
    omega
  have hAp : (B.restrict (plus t)).IsAlt := fun x => hA.self_eq_zero x.val
  have hAm : (B.restrict (minus t)).IsAlt := fun x => hA.self_eq_zero x.val
  have hCp : (C.restrict (plus s)).IsAlt := fun x => hCalt.self_eq_zero x.val
  have hCm : (C.restrict (minus s)).IsAlt := fun x => hCalt.self_eq_zero x.val
  obtain ⟨ep,hep⟩ := isometry_exists_of_finrank_eq (B.restrict (plus t)) hAp
    (plus_nondegenerate B hB t ht hp h2) (C.restrict (plus s)) hCp
    (plus_nondegenerate C hC s hs hsp h2) hpd
  obtain ⟨em,hem⟩ := isometry_exists_of_finrank_eq (B.restrict (minus t)) hAm
    (minus_nondegenerate B hB t ht hp h2) (C.restrict (minus s)) hCm
    (minus_nondegenerate C hC s hs hsp h2) hm
  exact ⟨conjugator t s ht hs h2 ep em,
    conjugator_preserves B C t s ht hs hp hsp h2 ep em hep hem,
    conjugator_intertwines t s ht hs h2 ep em⟩

/-- Actual symplectic conjugacy of involutions with equal minus-eigenspace dimensions. -/
theorem involution_conjugacy (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate)
    (t s : V →ₗ[F] V) (ht : Function.Involutive t) (hs : Function.Involutive s)
    (hp : ∀ x y, B (t x) (t y) = B x y) (hsp : ∀ x y, B (s x) (s y) = B x y)
    (h2 : (2 : F) ≠ 0) (hm : Module.finrank F (minus t) = Module.finrank F (minus s)) :
    ∃ g : V ≃ₗ[F] V, (∀ x y, B (g x) (g y) = B x y) ∧ (∀ x, g (t (g.symm x)) = s x) := by
  obtain ⟨g,hg,hgt⟩ := involution_isometry_exists B hA hB B hA hB t s ht hs hp hsp h2 rfl hm
  refine ⟨g,hg,?_⟩
  intro x
  rw [hgt,LinearEquiv.apply_symm_apply]

end Atlas.AlternatingForm
