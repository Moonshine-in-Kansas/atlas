import Atlas.LinearGroups.ReeF4.SpecialOppositePoints

/-! The actual intrinsic group preserves polar opposition. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem model_preserves_polar {m : ℕ} (g : Model F m) (u v : TraceZero F) :
    traceZeroPolar (g.val u) (g.val v) = traceZeroPolar u v := by
  obtain ⟨hp,_⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  exact traceZeroPolar_of_quadratic g.val
    (traceZeroStabilizer_quadratic ⟨g.val,hp⟩) u v

theorem specialOpposite_model_iff (m : ℕ) (g : Model F m)
    (p q : SpecialPoints (F := F) m) :
    SpecialOpposite m (g • p) (g • q) ↔ SpecialOpposite m p q := by
  have hrep (r : SpecialPoints (F := F) m) :
      (g • r).val = Projectivization.mk F (g.val r.val.rep)
        (fun h => r.val.rep_nonzero (g.val.injective (h.trans (map_zero g.val).symm))) := by
    calc
      (g • r).val = g.val • r.val := rfl
      _ = g.val • Projectivization.mk F r.val.rep r.val.rep_nonzero :=
        congrArg (fun z => g.val • z) (Projectivization.mk_rep r.val).symm
      _ = _ := rfl
  unfold SpecialOpposite
  rw [hrep p,hrep q,polar_nonzero_mk_reps_iff,model_preserves_polar]

end Atlas.ReeF4
