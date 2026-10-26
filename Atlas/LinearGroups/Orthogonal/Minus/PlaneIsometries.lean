import Atlas.LinearGroups.Orthogonal.Minus.NormPlane
import Atlas.LinearGroups.Orthogonal.Basic

/-! Full isometries of the anisotropic norm plane, in every characteristic. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

abbrev PlaneO (hdeg : Module.finrank F K = 2) := ↥(isometrySubgroup (normForm hdeg))

instance finite_planeO (hdeg : Module.finrank F K = 2) : Finite (PlaneO hdeg) :=
  Finite.of_injective (fun g : PlaneO hdeg => (g.val : K → K))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

/-- Actual scalar multiplication by a norm-one unit. -/
def planeScalar (hdeg : Module.finrank F K = 2) (u : normOne F K) : PlaneO hdeg :=
  ⟨{ toFun := fun z => (u.val : K)*z
     invFun := fun z => ((u.val⁻¹ : Kˣ) : K)*z
     left_inv := by intro z; simp [← mul_assoc]
     right_inv := by intro z; simp [← mul_assoc]
     map_add' := by intro x y; ring
     map_smul' := by intro r z; simp [Algebra.smul_def, mul_left_comm] }, by
    intro z
    change norm F K ((u.val : K)*z) = norm F K z
    rw [map_mul]
    have hu : norm F K (u.val : K) = 1 := by
      have h := congrArg (fun t : Fˣ => (t : F)) u.prop
      exact h
    rw [hu, one_mul]⟩

@[simp] theorem planeScalar_apply (hdeg : Module.finrank F K = 2) (u : normOne F K) (z : K) :
    (planeScalar hdeg u).val z = (u.val : K)*z := rfl

/-- The nontrivial field involution is an actual linear norm isometry. -/
def planeConjugation (hdeg : Module.finrank F K = 2) : PlaneO hdeg :=
  ⟨(conjugation F K).toLinearEquiv, by
    intro z
    apply (algebraMap F K).injective
    simp only [normForm_apply, norm_formula hdeg, AlgEquiv.toLinearEquiv_apply,
      conjugation_conjugation hdeg]
    exact mul_comm _ _⟩

@[simp] theorem planeConjugation_apply (hdeg : Module.finrank F K = 2) (z : K) :
    (planeConjugation hdeg).val z = conjugation F K z := rfl

/-- The two algebraic roots with prescribed quadratic trace and norm. -/
theorem norm_trace_fibre_two (hdeg : Module.finrank F K = 2) (x y : K)
    (ht : trace F K y = trace F K x) (hn : norm F K y = norm F K x) :
    y = x ∨ y = conjugation F K x := by
  have ht' := congrArg (algebraMap F K) ht
  have hn' := congrArg (algebraMap F K) hn
  rw [trace_formula hdeg, trace_formula hdeg] at ht'
  rw [norm_formula hdeg, norm_formula hdeg] at hn'
  have hp : (y-x)*(y-conjugation F K x)=0 := by
    linear_combination y*ht' - hn'
  exact (mul_eq_zero.mp hp).imp sub_eq_zero.mp sub_eq_zero.mp

theorem plane_preserves_polar (hdeg : Module.finrank F K = 2) (g : PlaneO hdeg) (x y : K) :
    (normForm hdeg).polarBilin (g.val x) (g.val y) = (normForm hdeg).polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← map_add, g.prop, g.prop, g.prop]

theorem plane_fix_one_classification (hdeg : Module.finrank F K = 2) (g : PlaneO hdeg)
    (hg : g.val 1 = 1) : g = 1 ∨ g = planeConjugation hdeg := by
  have hpoint (x : K) : g.val x = x ∨ g.val x = conjugation F K x := by
    apply norm_trace_fibre_two hdeg x (g.val x)
    · have hp := plane_preserves_polar hdeg g x 1
      rw [hg, normForm_polar, normForm_polar, map_one, mul_one, mul_one] at hp
      exact hp
    · exact g.prop x
  by_cases hid : ∀ x, g.val x = x
  · left
    exact Subtype.ext (LinearEquiv.ext hid)
  · right
    push_neg at hid
    obtain ⟨u,hu⟩ := hid
    have hgu := (hpoint u).resolve_left hu
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g.val x = conjugation F K x
    rcases hpoint x with hx | hx
    · rcases hpoint (x+u) with hsum | hsum
      · rw [map_add, hx, hgu] at hsum
        exact False.elim (hu (hgu.trans (add_left_cancel hsum)))
      · rw [map_add, hx, hgu, map_add] at hsum
        exact hx.trans (add_right_cancel hsum)
    · exact hx

/-- The coefficient of an arbitrary isometry is its value at one. -/
def planeCoefficient (hdeg : Module.finrank F K = 2) (g : PlaneO hdeg) : normOne F K := by
  have hne : g.val 1 ≠ 0 := by
    intro he
    have hh := g.val.injective (he.trans (map_zero g.val).symm)
    exact one_ne_zero hh
  refine ⟨Units.mk0 (g.val 1) hne, ?_⟩
  apply (normOne_mem_iff hdeg _).mpr
  have h := congrArg (algebraMap F K) (g.prop 1)
  simpa only [normForm_apply, norm_formula hdeg, map_one, mul_one, Units.val_mk0] using h

@[simp] theorem planeCoefficient_val (hdeg : Module.finrank F K = 2) (g : PlaneO hdeg) :
    ((planeCoefficient hdeg g).val : K) = g.val 1 := rfl

/-- These two genuine linear families exhaust the full norm-plane isometry group. -/
theorem plane_isometry_classification (hdeg : Module.finrank F K = 2) (g : PlaneO hdeg) :
    ∃ u : normOne F K, g = planeScalar hdeg u ∨
      g = planeScalar hdeg u * planeConjugation hdeg := by
  let u := planeCoefficient hdeg g
  let h := (planeScalar hdeg u)⁻¹ * g
  have hh : h.val 1 = 1 := by
    change ((u.val⁻¹ : Kˣ) : K) * g.val 1 = 1
    change ((u.val⁻¹ : Kˣ) : K) * (u.val : K) = 1
    simp
  refine ⟨u, ?_⟩
  rcases plane_fix_one_classification hdeg h hh with he | he
  · left
    have he' := congrArg (fun t : PlaneO hdeg => planeScalar hdeg u * t) he
    simpa [h] using he'
  · right
    have he' := congrArg (fun t : PlaneO hdeg => planeScalar hdeg u * t) he
    simpa [h] using he'

theorem planeConjugation_ne_one (hdeg : Module.finrank F K = 2) :
    planeConjugation hdeg ≠ 1 := by
  intro he
  apply conjugation_ne_one hdeg
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun g : PlaneO hdeg => g.val x) he

/-- Scalar coefficient and the conjugation branch, before multiplication is
transported to a semidirect product. -/
def planeParameter (hdeg : Module.finrank F K = 2) (p : normOne F K × Bool) : PlaneO hdeg :=
  if p.2 then planeScalar hdeg p.1 * planeConjugation hdeg else planeScalar hdeg p.1

@[simp] theorem planeParameter_apply_one (hdeg : Module.finrank F K = 2)
    (p : normOne F K × Bool) : (planeParameter hdeg p).val 1 = (p.1.val : K) := by
  rcases p with ⟨u,b⟩
  cases b <;> simp [planeParameter]

theorem planeParameter_injective (hdeg : Module.finrank F K = 2) :
    Function.Injective (planeParameter hdeg (F := F) (K := K)) := by
  rintro ⟨u,b⟩ ⟨v,c⟩ he
  have hu : u = v := by
    apply Subtype.ext
    apply Units.ext
    have hh := congrArg (fun g : PlaneO hdeg => g.val 1) he
    simpa only [planeParameter_apply_one] using hh
  subst v
  congr 1
  cases b <;> cases c
  · rfl
  · change planeScalar hdeg u = planeScalar hdeg u * planeConjugation hdeg at he
    have hh : (1 : PlaneO hdeg) = planeConjugation hdeg := by
      apply mul_left_cancel (a := planeScalar hdeg u)
      simpa using he
    exact False.elim (planeConjugation_ne_one hdeg hh.symm)
  · change planeScalar hdeg u * planeConjugation hdeg = planeScalar hdeg u at he
    have hh : planeConjugation hdeg = (1 : PlaneO hdeg) := by
      apply mul_left_cancel (a := planeScalar hdeg u)
      simpa using he
    exact False.elim (planeConjugation_ne_one hdeg hh)
  · rfl

/-- Unique parameters for every actual full norm-plane isometry. -/
def planeParameterEquiv (hdeg : Module.finrank F K = 2) : normOne F K × Bool ≃ PlaneO hdeg :=
  Equiv.ofBijective (planeParameter hdeg) ⟨planeParameter_injective hdeg, by
    intro g
    obtain ⟨u,hu | hu⟩ := plane_isometry_classification hdeg g
    · exact ⟨(u,false), by simpa [planeParameter] using hu.symm⟩
    · exact ⟨(u,true), by simpa [planeParameter] using hu.symm⟩⟩

/-- The independent anisotropic-plane base of the full orthogonal order recursion. -/
theorem card_planeO (hdeg : Module.finrank F K = 2) :
    Nat.card (PlaneO hdeg) = 2 * (Nat.card F + 1) := by
  rw [← Nat.card_congr (planeParameterEquiv hdeg), Nat.card_prod, normOne_card hdeg]
  simp [Nat.card_eq_fintype_card, mul_comm]
@[simp] theorem planeScalar_one (hdeg : Module.finrank F K = 2) :
    planeScalar hdeg (1 : normOne F K) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (1 : K)*x = x
  exact one_mul x

@[simp] theorem planeScalar_mul (hdeg : Module.finrank F K = 2) (u v : normOne F K) :
    planeScalar hdeg (u*v) = planeScalar hdeg u * planeScalar hdeg v := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change ((u.val : K)*(v.val : K))*x = (u.val : K)*((v.val : K)*x)
  exact mul_assoc _ _ _

/-- The cyclic scalar factor is mapped into the actual plane isometry group. -/
def planeScalarHom (hdeg : Module.finrank F K = 2) : normOne F K →* PlaneO hdeg where
  toFun := planeScalar hdeg
  map_one' := planeScalar_one hdeg
  map_mul' := planeScalar_mul hdeg

theorem planeScalarHom_injective (hdeg : Module.finrank F K = 2) :
    Function.Injective (planeScalarHom hdeg (F := F) (K := K)) := by
  intro u v he
  apply Subtype.ext
  apply Units.ext
  have h := congrArg (fun g : PlaneO hdeg => g.val 1) he
  simpa [planeScalarHom] using h

@[simp] theorem planeConjugation_mul_self (hdeg : Module.finrank F K = 2) :
    planeConjugation hdeg * planeConjugation hdeg = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact conjugation_conjugation hdeg x

theorem conjugation_normOne_eq_inv (hdeg : Module.finrank F K = 2) (u : normOne F K) :
    conjugation F K (u.val : K) = ((u.val⁻¹ : Kˣ) : K) := by
  apply mul_left_cancel₀ u.val.ne_zero
  rw [(normOne_mem_iff hdeg u.val).mp u.prop]
  simp

/-- The nontrivial involution acts on the norm-one scalar factor by inversion. -/
theorem planeConjugation_mul_scalar (hdeg : Module.finrank F K = 2) (u : normOne F K) :
    planeConjugation hdeg * planeScalar hdeg u =
      planeScalar hdeg u⁻¹ * planeConjugation hdeg := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change conjugation F K ((u.val : K)*x) = ((u.val⁻¹ : Kˣ) : K)*conjugation F K x
  rw [map_mul, conjugation_normOne_eq_inv hdeg]

theorem planeConjugation_conj_scalar (hdeg : Module.finrank F K = 2) (u : normOne F K) :
    planeConjugation hdeg * planeScalar hdeg u * (planeConjugation hdeg)⁻¹ =
      planeScalar hdeg u⁻¹ := by
  rw [planeConjugation_mul_scalar, mul_assoc, mul_inv_cancel, mul_one]

theorem planeConjugation_scalar_conjugation (hdeg : Module.finrank F K = 2)
    (u : normOne F K) : planeConjugation hdeg * (planeScalar hdeg u * planeConjugation hdeg) =
      planeScalar hdeg u⁻¹ := by
  rw [← mul_assoc, planeConjugation_mul_scalar, mul_assoc, planeConjugation_mul_self, mul_one]

/-- The explicit multiplication of norm-one coefficient and involution branch. -/
def planeParameterMul (p q : normOne F K × Bool) : normOne F K × Bool :=
  (p.1 * (if p.2 then q.1⁻¹ else q.1), Bool.xor p.2 q.2)

/-- The unique parameter bijection has precisely the semidirect multiplication
law for the cyclic norm-one group acted on by inversion. -/
theorem planeParameter_mul (hdeg : Module.finrank F K = 2) (p q : normOne F K × Bool) :
    planeParameter hdeg (planeParameterMul p q) = planeParameter hdeg p * planeParameter hdeg q := by
  rcases p with ⟨u,b⟩
  rcases q with ⟨v,c⟩
  cases b <;> cases c <;>
    simp [planeParameter, planeParameterMul, mul_assoc, planeConjugation_mul_scalar,
      planeConjugation_scalar_conjugation]
end Atlas.Orthogonal.Minus
