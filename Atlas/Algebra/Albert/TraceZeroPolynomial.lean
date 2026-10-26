import Atlas.Algebra.Albert.TraceZeroForms
import Atlas.Algebra.Albert.ScalarMap

/-! Actual polynomials on the 26 independent trace-zero coordinates.
These remain polynomials over small finite fields, not equivalence classes
of polynomial functions. Evaluation is a theorem, not the definition of
polynomial preservation. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

abbrev TraceZeroCoordinate := Fin 2 ⊕ (Fin 3 × Fin 8)

def traceZeroCoordinateEquiv : TraceZero F ≃ₗ[F] (TraceZeroCoordinate → F) :=
  traceZeroCoordinatesEquiv.trans
    { toFun := fun x => Sum.elim x.1 (fun i => x.2 i.1 i.2)
      invFun := fun x => (fun i => x (.inl i), fun i j => x (.inr (i,j)))
      left_inv := fun _ => rfl
      right_inv := fun x => by funext i; cases i <;> rfl
      map_add' := fun _ _ => by funext i; cases i <;> rfl
      map_smul' := fun _ _ => by funext i; cases i <;> rfl }

def universalTraceZero : TraceZero (MvPolynomial TraceZeroCoordinate F) :=
  let x : TraceZeroCoordinate → MvPolynomial TraceZeroCoordinate F := MvPolynomial.X
  ⟨(![x (.inl 0), x (.inl 1), -(x (.inl 0) + x (.inl 1))],
      fun i j => x (.inr (i,j))), by
    change x (.inl 0) + x (.inl 1) + -(x (.inl 0) + x (.inl 1)) = 0
    exact add_neg_cancel _⟩

def traceZeroQuadraticPolynomial : MvPolynomial TraceZeroCoordinate F :=
  quadraticTrace (universalTraceZero (F:=F))

def traceZeroCubicPolynomial : MvPolynomial TraceZeroCoordinate F :=
  norm (universalTraceZero (F:=F))

theorem eval_universalTraceZero (w : TraceZero F) :
    map (MvPolynomial.eval (traceZeroCoordinateEquiv w))
      (universalTraceZero (F:=F) : Carrier (MvPolynomial TraceZeroCoordinate F)) = w := by
  apply Prod.ext
  · funext i
    fin_cases i
    · simp only [map, universalTraceZero, Matrix.cons_val_zero', Matrix.cons_val_succ', MvPolynomial.eval_X]
      rfl
    · simp only [map, universalTraceZero, Matrix.cons_val_zero', Matrix.cons_val_succ', MvPolynomial.eval_X]
      rfl
    · simp only [map, universalTraceZero, Matrix.cons_val_zero', Matrix.cons_val_succ',
        _root_.map_neg, _root_.map_add, MvPolynomial.eval_X]
      change -(w.val.1 0 + w.val.1 1) = w.val.1 2
      have h := w.property
      change w.val.1 0 + w.val.1 1 + w.val.1 2 = 0 at h
      linear_combination -h
  · funext i j
    change MvPolynomial.eval (traceZeroCoordinateEquiv w)
      (MvPolynomial.X (.inr (i,j))) = w.val.2 i j
    rw [MvPolynomial.eval_X]
    rfl

@[simp] theorem eval_traceZeroQuadraticPolynomial (w : TraceZero F) :
    MvPolynomial.eval (traceZeroCoordinateEquiv w) traceZeroQuadraticPolynomial =
      traceZeroQuadratic w := by
  rw [traceZeroQuadraticPolynomial, ← quadraticTrace_map, eval_universalTraceZero]
  rfl

@[simp] theorem eval_traceZeroCubicPolynomial (w : TraceZero F) :
    MvPolynomial.eval (traceZeroCoordinateEquiv w) traceZeroCubicPolynomial =
      traceZeroCubic w := by
  rw [traceZeroCubicPolynomial, ← norm_map, eval_universalTraceZero]
  rfl

end Atlas.Albert
