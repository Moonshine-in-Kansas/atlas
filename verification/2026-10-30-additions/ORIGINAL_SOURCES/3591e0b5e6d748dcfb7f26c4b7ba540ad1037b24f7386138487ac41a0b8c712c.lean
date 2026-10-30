import FamilyWork.TorusAnchors
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! fixed unit tuples in the public E6 simple-node numbering.

The carrier is literally the subgroup of functions `Fin 6 → Kˣ` satisfying
`conjugationUnits F K (t i) = t (simpleNode i)`. Its multiplicative parameters
are `((a,b),(u,v)) ↦ [u, embed a, v, embed b, σ v, σ u]`.

This file proves no identification with the actual fixed torus. That action
and identification are separate work. Verification receipts are recorded separately.
-/

noncomputable section

namespace Atlas.Chevalley.TwistedE6.TorusUnitParameters

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The actual base-field inclusion on units. -/
def embedUnits : Fˣ →* Kˣ :=
  Units.map (algebraMap F K).toMonoidHom

@[simp] theorem embedUnits_val (a : Fˣ) :
    (embedUnits F K a : K) = algebraMap F K (a : F) := rfl

theorem embedUnits_injective : Function.Injective (embedUnits F K) := by
  intro a b h
  apply Units.ext
  apply (algebraMap F K).injective
  exact congrArg (fun u : Kˣ => (u : K)) h

@[simp] theorem conjugationUnits_val (u : Kˣ) :
    (conjugationUnits F K u : K) = Atlas.FiniteQuadratic.conjugation F K (u : K) := rfl

@[simp] theorem conjugationUnits_embedUnits (a : Fˣ) :
    conjugationUnits F K (embedUnits F K a) = embedUnits F K a := by
  apply Units.ext
  exact Atlas.FiniteQuadratic.conjugation_base F K (a : F)

theorem conjugationUnits_involutive (hdeg : Module.finrank F K = 2) :
    Function.Involutive (conjugationUnits F K) := by
  intro u
  apply Units.ext
  exact Atlas.FiniteQuadratic.conjugation_conjugation hdeg (u : K)

@[simp] theorem conjugationUnits_conjugationUnits (hdeg : Module.finrank F K = 2)
    (u : Kˣ) : conjugationUnits F K (conjugationUnits F K u) = u :=
  conjugationUnits_involutive F K hdeg u

/-- A conjugation-fixed extension unit comes from an actual base-field unit.
Nonvanishing descends along the same algebra map as the fixed scalar. -/
theorem conjugationUnits_fixed_iff (hdeg : Module.finrank F K = 2) (u : Kˣ) :
    conjugationUnits F K u = u ↔ ∃ a : Fˣ, embedUnits F K a = u := by
  constructor
  · intro hu
    have hx : Atlas.FiniteQuadratic.conjugation F K (u : K) = (u : K) :=
      congrArg (fun v : Kˣ => (v : K)) hu
    obtain ⟨a, ha⟩ := (Atlas.FiniteQuadratic.conjugation_fixed_iff hdeg (u : K)).mp hx
    have ha0 : a ≠ 0 := by
      intro h
      apply u.ne_zero
      rw [← ha, h, map_zero]
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Units.ext
    exact ha
  · rintro ⟨a, rfl⟩
    exact conjugationUnits_embedUnits F K a

/-- The literal fixed-tuple condition, using public simple-node labels. -/
def fixedUnitTuples : Subgroup (Fin 6 → Kˣ) where
  carrier := {t | ∀ i, conjugationUnits F K (t i) = t (simpleNode i)}
  one_mem' := by
    intro i
    exact map_one (conjugationUnits F K)
  mul_mem' := by
    intro s t hs ht i
    change conjugationUnits F K (s i * t i) = s (simpleNode i) * t (simpleNode i)
    rw [map_mul, hs i, ht i]
  inv_mem' := by
    intro t ht i
    change conjugationUnits F K ((t i)⁻¹) = (t (simpleNode i))⁻¹
    rw [map_inv, ht i]

@[simp] theorem mem_fixedUnitTuples (t : Fin 6 → Kˣ) :
    t ∈ fixedUnitTuples F K ↔
      ∀ i, conjugationUnits F K (t i) = t (simpleNode i) := Iff.rfl

/-- Fixed coordinates 1,3 and smaller paired coordinates 0,2, in that order. -/
abbrev Parameters := (Fˣ × Fˣ) × (Kˣ × Kˣ)

/-- The literal tuple `[u, embed a, v, embed b, σ v, σ u]`.
Here `simpleNode = [5,1,4,3,2,0]`, not the lattice-coordinate permutation. -/
def expand (p : Parameters F K) : Fin 6 → Kˣ :=
  ![p.2.1, embedUnits F K p.1.1, p.2.2, embedUnits F K p.1.2,
    conjugationUnits F K p.2.2, conjugationUnits F K p.2.1]

theorem expand_mem (hdeg : Module.finrank F K = 2) (p : Parameters F K) :
    expand F K p ∈ fixedUnitTuples F K := by
  intro i
  fin_cases i
  · rfl
  · exact conjugationUnits_embedUnits F K p.1.1
  · rfl
  · exact conjugationUnits_embedUnits F K p.1.2
  · exact conjugationUnits_conjugationUnits F K hdeg p.2.2
  · exact conjugationUnits_conjugationUnits F K hdeg p.2.1

/-- Componentwise multiplication makes the explicit expansion a homomorphism. -/
def parameterHom (hdeg : Module.finrank F K = 2) :
    Parameters F K →* fixedUnitTuples F K where
  toFun p := ⟨expand F K p, expand_mem F K hdeg p⟩
  map_one' := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [expand]
  map_mul' p q := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [expand, map_mul]

@[simp] theorem parameterHom_val (hdeg : Module.finrank F K = 2) (p : Parameters F K) :
    (parameterHom F K hdeg p).val = expand F K p := rfl

/-- Coordinates 1,3 recover the base units; coordinates 0,2 recover the free units. -/
theorem parameterHom_injective (hdeg : Module.finrank F K = 2) :
    Function.Injective (parameterHom F K hdeg) := by
  intro p q hpq
  have h : expand F K p = expand F K q := by
    simpa only [parameterHom_val] using congrArg Subtype.val hpq
  apply Prod.ext
  · apply Prod.ext
    · apply embedUnits_injective F K
      exact congrFun h 1
    · apply embedUnits_injective F K
      exact congrFun h 3
  · apply Prod.ext
    · exact congrFun h 0
    · exact congrFun h 2

/-- Every tuple in the literal subgroup has the displayed form. -/
theorem parameterHom_surjective (hdeg : Module.finrank F K = 2) :
    Function.Surjective (parameterHom F K hdeg) := by
  intro t
  have h1 : conjugationUnits F K (t.val 1) = t.val 1 := t.property 1
  have h3 : conjugationUnits F K (t.val 3) = t.val 3 := t.property 3
  obtain ⟨a, ha⟩ := (conjugationUnits_fixed_iff F K hdeg (t.val 1)).mp h1
  obtain ⟨b, hb⟩ := (conjugationUnits_fixed_iff F K hdeg (t.val 3)).mp h3
  refine ⟨((a, b), (t.val 0, t.val 2)), ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · rfl
  · exact ha
  · rfl
  · exact hb
  · exact t.property 2
  · exact t.property 0

/-- Multiplicative equivalence of the parameter groups and the full fixed-tuple subgroup. -/
def parametersEquiv (hdeg : Module.finrank F K = 2) :
    Parameters F K ≃* fixedUnitTuples F K :=
  MulEquiv.ofBijective (parameterHom F K hdeg)
    ⟨parameterHom_injective F K hdeg, parameterHom_surjective F K hdeg⟩

@[simp] theorem parametersEquiv_val (hdeg : Module.finrank F K = 2) (p : Parameters F K) :
    (parametersEquiv F K hdeg p).val = expand F K p := rfl

/-- The inverse reads its two extension units at public nodes 0 and 2. -/
theorem parametersEquiv_symm_extension (hdeg : Module.finrank F K = 2)
    (t : fixedUnitTuples F K) :
    ((parametersEquiv F K hdeg).symm t).2 = (t.val 0, t.val 2) := by
  have h : expand F K ((parametersEquiv F K hdeg).symm t) = t.val := by
    simpa only [parametersEquiv_val] using
      congrArg Subtype.val ((parametersEquiv F K hdeg).apply_symm_apply t)
  apply Prod.ext
  · exact congrFun h 0
  · exact congrFun h 2

/-- The inverse descends its two fixed coordinates along the actual base inclusion. -/
theorem parametersEquiv_symm_base (hdeg : Module.finrank F K = 2)
    (t : fixedUnitTuples F K) :
    (embedUnits F K ((parametersEquiv F K hdeg).symm t).1.1,
      embedUnits F K ((parametersEquiv F K hdeg).symm t).1.2) = (t.val 1, t.val 3) := by
  have h : expand F K ((parametersEquiv F K hdeg).symm t) = t.val := by
    simpa only [parametersEquiv_val] using
      congrArg Subtype.val ((parametersEquiv F K hdeg).apply_symm_apply t)
  apply Prod.ext
  · exact congrFun h 1
  · exact congrFun h 3

theorem parameters_card :
    Nat.card (Parameters F K) = (Nat.card F - 1) ^ 2 * (Nat.card K - 1) ^ 2 := by
  change Nat.card ((Fˣ × Fˣ) × (Kˣ × Kˣ)) = _
  simp only [Nat.card_prod, Nat.card_units, pow_two]

/-- Uniform count of the literal fixed-unit tuples. This is not yet a torus-order theorem. -/
theorem fixedUnitTuples_card (hdeg : Module.finrank F K = 2) :
    Nat.card (fixedUnitTuples F K) = (Nat.card F - 1) ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
  calc
    _ = Nat.card (Parameters F K) :=
      (Nat.card_congr (parametersEquiv F K hdeg).toEquiv).symm
    _ = (Nat.card F - 1) ^ 2 * (Nat.card K - 1) ^ 2 := parameters_card F K
    _ = (Nat.card F - 1) ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
      rw [Atlas.FiniteQuadratic.card_extension hdeg]

end Atlas.Chevalley.TwistedE6.TorusUnitParameters
