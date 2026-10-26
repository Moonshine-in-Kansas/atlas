import Atlas.Algebra.Albert.TraceZeroForms

/-! Extending actual linear transformations of the trace kernel by fixing the
unit line. These identities work over coefficient rings, including polynomial
rings; they do not assert that equality of finite-field functions implies
polynomial equality. -/
namespace Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def traceZeroSplitEquiv : Carrier F ≃ₗ[F] F × TraceZero F where
  toFun x := (trace x, traceZeroProjection x)
  invFun p := p.1 • unit + (p.2 : Carrier F)
  left_inv x := traceZero_decomposition x
  right_inv p := by
    apply Prod.ext
    · change traceLinear (p.1 • unit + (p.2 : Carrier F)) = p.1
      rw [map_add, map_smul]
      change p.1 * trace unit + trace (p.2 : Carrier F) = p.1
      simp
    · simp only [map_add, map_smul, traceZeroProjection_unit,
        smul_zero, traceZeroProjection_coe, zero_add]
  map_add' x y := by
    apply Prod.ext
    · exact (traceLinear (F:=F)).map_add x y
    · exact traceZeroProjection.map_add x y
  map_smul' a x := by
    apply Prod.ext
    · exact (traceLinear (F:=F)).map_smul a x
    · exact traceZeroProjection.map_smul a x

def traceZeroExtend (g : TraceZero F ≃ₗ[F] TraceZero F) : Carrier F ≃ₗ[F] Carrier F :=
  traceZeroSplitEquiv.trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl F F) g).trans traceZeroSplitEquiv.symm)

@[simp] theorem traceZeroExtend_apply (g : TraceZero F ≃ₗ[F] TraceZero F)
    (x : Carrier F) : traceZeroExtend g x =
      trace x • unit + (g (traceZeroProjection x) : Carrier F) := rfl

@[simp] theorem traceZeroExtend_coe (g : TraceZero F ≃ₗ[F] TraceZero F)
    (w : TraceZero F) : traceZeroExtend g (w : Carrier F) = (g w : Carrier F) := by
  simp

@[simp] theorem traceZeroExtend_unit (g : TraceZero F ≃ₗ[F] TraceZero F) :
    traceZeroExtend g unit = unit := by simp

theorem traceZeroExtend_norm (g : TraceZero F ≃ₗ[F] TraceZero F)
    (hQ : ∀ w, traceZeroQuadratic (g w) = traceZeroQuadratic w)
    (hC : ∀ w, traceZeroCubic (g w) = traceZeroCubic w)
    (x : Carrier F) : norm (traceZeroExtend g x) = norm x := by
  rw [traceZeroExtend_apply, traceZeroCubicDecomposition, hQ, hC,
    ← traceZeroCubicDecomposition, traceZero_decomposition]

theorem traceZeroExtend_norm_iff (g : TraceZero F ≃ₗ[F] TraceZero F) :
    (∀ x, norm (traceZeroExtend g x) = norm x) ↔
      (∀ w, traceZeroQuadratic (g w) = traceZeroQuadratic w) ∧
      (∀ w, traceZeroCubic (g w) = traceZeroCubic w) := by
  constructor
  · intro h
    have hC : ∀ w, traceZeroCubic (g w) = traceZeroCubic w := by
      intro w
      simpa only [traceZeroCubic, traceZeroExtend_coe] using h (w : Carrier F)
    refine ⟨?_, hC⟩
    intro w
    rw [traceZeroQuadratic_constantTerm, traceZeroQuadratic_constantTerm,
      ← traceZeroExtend_coe, h, ← traceZeroExtend_unit g,
      ← map_add, h, traceZeroExtend_unit]
  · rintro ⟨hQ,hC⟩
    exact traceZeroExtend_norm g hQ hC

end Atlas.Albert
