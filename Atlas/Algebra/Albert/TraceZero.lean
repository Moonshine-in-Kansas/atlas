import Atlas.Algebra.Albert.Cubic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-! The actual trace kernel of the existing Albert space, with 26 independent
coordinates. The characteristic-two projection retains the distinguished unit. -/
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

def traceLinear : Carrier F →ₗ[F] F where
  toFun := trace
  map_add' x y := by simp [trace]; ring
  map_smul' a x := by simp [trace]; ring

abbrev TraceZero (F : Type*) [CommRing F] := (traceLinear (F:=F)).ker

@[simp] theorem trace_traceZero (w : TraceZero F) : trace (w : Carrier F) = 0 := w.property

abbrev TraceZeroCoordinates (F : Type*) := (Fin 2 → F) × (Fin 3 → SplitOctonion.Carrier F)

def traceZeroCoordinatesEquiv : TraceZero F ≃ₗ[F] TraceZeroCoordinates F where
  toFun w := (fun i => w.val.1 (Fin.castLE (by decide) i), w.val.2)
  invFun w := ⟨(![w.1 0, w.1 1, -(w.1 0 + w.1 1)], w.2), by
    change w.1 0 + w.1 1 + -(w.1 0 + w.1 1) = 0
    exact add_neg_cancel _⟩
  left_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      fin_cases i <;> simp
      have h := w.property
      change w.val.1 0 + w.val.1 1 + w.val.1 2 = 0 at h
      linear_combination -h
    · rfl
  right_inv w := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem traceZero_finrank {K : Type*} [Field K] : Module.finrank K (TraceZero K) = 26 := by
  rw [(traceZeroCoordinatesEquiv (F:=K)).finrank_eq]
  simp [TraceZeroCoordinates, SplitOctonion.Carrier, Module.finrank_pi_fintype]

variable [CharP F 2]

@[simp] theorem trace_unit_charTwo : trace (unit : Carrier F) = 1 := by
  simp [trace, unit, CharTwo.add_self_eq_zero]

def traceZeroProjection : Carrier F →ₗ[F] TraceZero F where
  toFun x := ⟨x - trace x • unit, by
    change traceLinear (x - trace x • unit) = 0
    simp only [map_sub, map_smul]
    change trace x - trace x * trace unit = 0
    simp⟩
  map_add' x y := by
    apply Subtype.ext
    change x + y - trace (x+y) • unit = _
    have ht : trace (x+y) = trace x + trace y := (traceLinear (F:=F)).map_add x y
    rw [ht, add_smul]
    simp only [Submodule.coe_add]
    abel
  map_smul' a x := by
    apply Subtype.ext
    change a • x - trace (a • x) • unit = a • (x - trace x • unit)
    have ht : trace (a • x) = a * trace x := (traceLinear (F:=F)).map_smul a x
    rw [ht, smul_sub, smul_smul]

@[simp] theorem traceZeroProjection_coe (w : TraceZero F) :
    traceZeroProjection (w : Carrier F) = w := by
  apply Subtype.ext
  change (w : Carrier F) - trace (w : Carrier F) • unit = (w : Carrier F)
  simp

@[simp] theorem traceZeroProjection_unit : traceZeroProjection (unit : Carrier F) = 0 := by
  apply Subtype.ext
  change unit - trace (unit : Carrier F) • unit = 0
  simp

theorem traceZero_decomposition (x : Carrier F) :
    trace x • unit + (traceZeroProjection x : Carrier F) = x := by
  change trace x • unit + (x - trace x • unit) = x
  abel

theorem traceZeroProjection_formula (x : Carrier F) :
    (traceZeroProjection x : Carrier F) = x + trace x • unit := by
  change x - trace x • unit = x + trace x • unit
  rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem traceZeroProjection_surjective : Function.Surjective (traceZeroProjection (F:=F)) :=
  fun w => ⟨w, traceZeroProjection_coe w⟩

theorem traceZeroProjection_ker :
    (traceZeroProjection (F:=F)).ker = Submodule.span F {(unit : Carrier F)} := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro h
    have hc := congrArg (fun w : TraceZero F => (w : Carrier F)) h
    change x - trace x • unit = 0 at hc
    exact ⟨trace x, (sub_eq_zero.mp hc).symm⟩
  · rintro ⟨a, rfl⟩
    rw [map_smul, traceZeroProjection_unit, smul_zero]

noncomputable def traceZeroQuotientEquiv :
    (Carrier F ⧸ Submodule.span F {(unit : Carrier F)}) ≃ₗ[F] TraceZero F :=
  (Submodule.quotEquivOfEq _ _ (traceZeroProjection_ker (F:=F)).symm).trans
    ((traceZeroProjection (F:=F)).quotKerEquivOfSurjective traceZeroProjection_surjective)

@[simp] theorem traceZeroQuotientEquiv_mk (x : Carrier F) :
    traceZeroQuotientEquiv (F:=F) (Submodule.Quotient.mk x) = traceZeroProjection x := by
  simp [traceZeroQuotientEquiv]

end Atlas.Albert
