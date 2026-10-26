import Atlas.Algebra.Albert.TraceZeroExtension
import Atlas.Algebra.Albert.StabilizerInvariants

/-! The full polynomial Albert stabilizer acts on the actual trace kernel.
The restriction determines the original transformation, since the unit is fixed. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def traceZeroRestrict (g : polynomialStabilizer (F:=F)) : TraceZero F ≃ₗ[F] TraceZero F where
  toFun w := ⟨g.val w, by
    change trace (g.val w) = 0
    rw [stabilizer_trace, trace_traceZero]⟩
  invFun w := ⟨(g⁻¹).val w, by
    change trace ((g⁻¹).val w) = 0
    rw [stabilizer_trace, trace_traceZero]⟩
  left_inv w := by apply Subtype.ext; exact g.val.symm_apply_apply w
  right_inv w := by apply Subtype.ext; exact g.val.apply_symm_apply w
  map_add' u v := by apply Subtype.ext; exact g.val.map_add u v
  map_smul' a w := by apply Subtype.ext; exact g.val.map_smul a w

@[simp] theorem traceZeroRestrict_coe (g : polynomialStabilizer (F:=F))
    (w : TraceZero F) : (traceZeroRestrict g w : Carrier F) = g.val w := rfl

@[simp] theorem traceZeroRestrict_quadratic (g : polynomialStabilizer (F:=F))
    (w : TraceZero F) : traceZeroQuadratic (traceZeroRestrict g w) = traceZeroQuadratic w :=
  stabilizer_quadraticTrace g w

@[simp] theorem traceZeroRestrict_cubic (g : polynomialStabilizer (F:=F))
    (w : TraceZero F) : traceZeroCubic (traceZeroRestrict g w) = traceZeroCubic w :=
  stabilizer_norm g w

@[simp] theorem traceZeroExtend_restrict (g : polynomialStabilizer (F:=F)) :
    traceZeroExtend (traceZeroRestrict g) = g.val := by
  apply LinearEquiv.ext
  intro x
  rw [traceZeroExtend_apply, traceZeroRestrict_coe, ← stabilizer_unit g,
    ← g.val.map_smul, ← g.val.map_add, traceZero_decomposition]

theorem traceZeroRestrict_injective : Function.Injective (traceZeroRestrict (F:=F)) := by
  intro g h he
  apply Subtype.ext
  rw [← traceZeroExtend_restrict g, ← traceZeroExtend_restrict h, he]

theorem traceZeroProjection_stabilizer (g : polynomialStabilizer (F:=F))
    (x : Carrier F) : traceZeroProjection (g.val x) =
      traceZeroRestrict g (traceZeroProjection x) := by
  apply Subtype.ext
  change g.val x - trace (g.val x) • unit = g.val (x - trace x • unit)
  rw [stabilizer_trace, map_sub, g.val.map_smul, stabilizer_unit]

theorem traceZeroRestrict_polar (g : polynomialStabilizer (F:=F))
    (u v : TraceZero F) : traceZeroPolar (traceZeroRestrict g u) (traceZeroRestrict g v) =
      traceZeroPolar u v := stabilizer_tracePairing g u v

theorem traceZeroRestrict_cross (g : polynomialStabilizer (F:=F))
    (u v : TraceZero F) : traceZeroCross (traceZeroRestrict g u) (traceZeroRestrict g v) =
      traceZeroRestrict g (traceZeroCross u v) := by
  unfold traceZeroCross
  rw [traceZeroRestrict_coe, traceZeroRestrict_coe, stabilizer_cross,
    traceZeroProjection_stabilizer]

end Atlas.Albert
