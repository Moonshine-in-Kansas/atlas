import Atlas.LinearAlgebra.BooleanSpinGamma
import Atlas.LinearGroups.Orthogonal.Basic

/-! The actual odd quadratic space maps injectively into the Boolean spin
endomorphisms. This is vector-map injectivity, not Clifford-algebra faithfulness. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Atlas.BooleanSpin
open scoped BigOperators

/-- The original quadratic coordinates, with no change of the odd quadratic form. -/
def spinGamma (r : ℕ) (R : Type*) [CommRing R] :
    Atlas.Orthogonal.VectorB r R →ₗ[R] Module.End R (Space (I := Fin r) R) where
  toFun v := gamma R (fun i => v.1 (.inl i)) (fun i => v.1 (.inr i)) v.2
  map_add' v w := by
    simp only [gamma, axis, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      add_smul, Finset.sum_add_distrib]
    module
  map_smul' a v := by
    simp only [gamma, axis, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      smul_eq_mul, mul_smul, smul_add, Finset.smul_sum, RingHom.id_apply]

/-- The vector map is injective even if 2=0 or the coefficient ring is trivial. -/
theorem spinGamma_injective (r : ℕ) (R : Type*) [CommRing R] :
    Function.Injective (spinGamma r R) := by
  intro v w h
  have he : ((fun i : Fin r => v.1 (.inl i)), (fun i => v.1 (.inr i)), v.2) =
      ((fun i : Fin r => w.1 (.inl i)), (fun i => w.1 (.inr i)), w.2) :=
    gamma_injective (I := Fin r) R h
  apply Prod.ext
  · funext i
    cases i with
    | inl i => exact congrFun (congrArg Prod.fst he) i
    | inr i => exact congrFun (congrArg (fun p => p.2.1) he) i
  · exact congrArg (fun p => p.2.2) he

/-- Exact agreement with the existing all-characteristic odd quadratic form. -/
theorem spinGamma_square (r : ℕ) (R : Type*) [CommRing R]
    (v : Atlas.Orthogonal.VectorB r R) :
    spinGamma r R v * spinGamma r R v = Atlas.Orthogonal.formB r R v • 1 := by
  simpa only [spinGamma, LinearMap.coe_mk, AddHom.coe_mk,
    Atlas.Orthogonal.formB_apply, Atlas.Orthogonal.formD_apply] using
      gamma_square R (fun i => v.1 (.inl i)) (fun i => v.1 (.inr i)) v.2

/-- On the odd polar radical in characteristic two, conjugation sees a scalar. -/
theorem spinGamma_radical_charTwo (r : ℕ) (R : Type*) [CommRing R]
    (h2 : (2 : R) = 0) (z : R) :
    spinGamma r R (0,z) = z • 1 :=
  gamma_radical_charTwo (I := Fin r) R h2 z

@[simp] theorem spinGamma_e (r : ℕ) (R : Type*) [CommRing R] (i : Fin r) (a : R) :
    spinGamma r R (Pi.single (.inl i) a, 0) = a • creation R i := by
  classical
  simp [spinGamma, gamma, axis, Pi.single_apply, eq_comm]

@[simp] theorem spinGamma_f (r : ℕ) (R : Type*) [CommRing R] (i : Fin r) (a : R) :
    spinGamma r R (Pi.single (.inr i) a, 0) = a • annihilation R i := by
  classical
  simp [spinGamma, gamma, axis, Pi.single_apply, eq_comm]

@[simp] theorem spinGamma_z (r : ℕ) (R : Type*) [CommRing R] (a : R) :
    spinGamma r R (0,a) = a • parity (I := Fin r) R := by
  simp [spinGamma, gamma, axis]

end Atlas.Chevalley.Comparison.TypeB

