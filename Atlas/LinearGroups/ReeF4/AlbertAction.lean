import Atlas.Algebra.Albert.TraceZeroRestriction
import Atlas.LinearGroups.ReeF4.StarDomain

/-! The ambient Albert stabilizer acts faithfully on the partial-product domain.
This does not assert preservation of the as-yet-unconstructed Ree star map. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

def albertAction : polynomialStabilizer (F:=F) →* (TraceZero F ≃ₗ[F] TraceZero F) where
  toFun := traceZeroRestrict
  map_one' := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rfl

theorem albertAction_injective : Function.Injective (albertAction (F:=F)) :=
  traceZeroRestrict_injective

theorem starDomain_albertAction_iff (g : polynomialStabilizer (F:=F))
    (u v : TraceZero F) : StarDomain (albertAction g u) (albertAction g v) ↔ StarDomain u v := by
  change (traceZeroPolar (traceZeroRestrict g u) (traceZeroRestrict g v) = 0 ∧
    traceZeroCross (traceZeroRestrict g u) (traceZeroRestrict g v) = 0) ↔ _
  rw [traceZeroRestrict_polar, traceZeroRestrict_cross]
  constructor
  · rintro ⟨hb,hc⟩
    refine ⟨hb, (traceZeroRestrict g).injective ?_⟩
    rw [hc, map_zero]
  · rintro ⟨hb,hc⟩
    refine ⟨hb, ?_⟩
    rw [hc, map_zero]

end Atlas.ReeF4
