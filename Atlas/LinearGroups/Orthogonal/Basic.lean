import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! # Standard split and odd quadratic spaces, without division by two -/
noncomputable section
namespace Atlas.Orthogonal

abbrev Index (n : ℕ) := Fin n ⊕ Fin n
abbrev VectorD (n : ℕ) (F : Type*) := Index n → F
abbrev VectorB (n : ℕ) (F : Type*) := VectorD n F × F

variable {n : ℕ} {F : Type*} [CommRing F]

/-- The split quadratic form on the ordered hyperbolic coordinates. -/
def formD (n : ℕ) (F : Type*) [CommRing F] : QuadraticForm F (VectorD n F) :=
  ∑ i : Fin n, QuadraticMap.proj (R := F) (.inl i) (.inr i)

/-- The odd-dimensional quadratic form, including its anisotropic last coordinate. -/
def formB (n : ℕ) (F : Type*) [CommRing F] : QuadraticForm F (VectorB n F) :=
  (formD n F).comp (LinearMap.fst F _ _) +
    (QuadraticMap.sq (R := F)).comp (LinearMap.snd F _ _)

@[simp] theorem formD_apply (v : VectorD n F) :
    formD n F v = ∑ i : Fin n, v (.inl i) * v (.inr i) := by
  simp [formD, QuadraticMap.proj, QuadraticMap.linMulLin_apply]

@[simp] theorem formB_apply (v : VectorB n F) :
    formB n F v = formD n F v.1 + v.2 ^ 2 := by
  simp [formB, QuadraticMap.sq, QuadraticMap.linMulLin_apply, pow_two]

/-- Full linear isometries of a quadratic form, with the ordinary composition law. -/
def isometrySubgroup {V : Type*} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ v, Q (g v) = Q v}
  one_mem' := fun _ => rfl
  mul_mem' hg hh v := (hg _).trans (hh v)
  inv_mem' {g} hg v := by
    have h := hg (g.symm v)
    simpa using h.symm

abbrev O_B (n : ℕ) (F : Type*) [CommRing F] := ↥(isometrySubgroup (formB n F))
abbrev O_DPlus (n : ℕ) (F : Type*) [CommRing F] := ↥(isometrySubgroup (formD n F))

/-- The primary carrier is exactly the full quadratic-isometry carrier. -/
def isometryCarrierEquiv {V : Type*} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) : ↥(isometrySubgroup Q) ≃ Q.IsometryEquiv Q where
  toFun g := { g.val with map_app' := g.prop }
  invFun g := ⟨g.toLinearEquiv, g.map_app⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance finite_orthogonal_b [Finite F] : Finite (O_B n F) :=
  Finite.of_injective (fun g : O_B n F => (g.val : VectorB n F → VectorB n F))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))
instance finite_orthogonal_d [Finite F] : Finite (O_DPlus n F) :=
  Finite.of_injective (fun g : O_DPlus n F => (g.val : VectorD n F → VectorD n F))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

/-- Polarization of the split form is nondegenerate even in characteristic two. -/
theorem polarD_apply (u v : VectorD n F) :
    (formD n F).polarBilin u v =
      ∑ i : Fin n, (u (.inl i) * v (.inr i) + v (.inl i) * u (.inr i)) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, formD_apply, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polarB_apply (u v : VectorB n F) :
    (formB n F).polarBilin u v = (formD n F).polarBilin u.1 v.1 + 2 * u.2 * v.2 := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, formB_apply,
    Prod.fst_add, Prod.snd_add]
  ring

end Atlas.Orthogonal
