import Atlas.Conway.EisensteinBalancedFamily
import Atlas.Conway.EisensteinHexadPhaseAction
import Atlas.Conway.EisensteinFrameOrder
import Atlas.Codes.TernaryBalancedAction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

def eisensteinBalancedPhaseFromCode (c : TernaryBalancedWords) (t : ternaryGolay) :
    EisensteinBalancedPhase c :=
  ⟨fun i => t.val i.val,ternaryHexadRestriction_le (ternaryBalancedSixWord c)
    ⟨t,rfl⟩⟩

theorem eisensteinBalancedPhasedVector_fromCode (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (t : ternaryGolay) :
    eisensteinBalancedPhasedVector c j (eisensteinBalancedPhaseFromCode c t) =
      eisensteinDiagonal t.val (eisensteinBalancedHexadVector c j.val) := by
  funext i
  by_cases hi : i ∈ ternarySupport c.val.val
  · simp [eisensteinBalancedPhasedVector,eisensteinDiagonal,eisensteinBalancedPhaseWord,
      eisensteinBalancedPhaseFromCode,hi]
  · have hz : c.val.val i=0 := by simpa [ternarySupport] using hi
    have hij : i≠j.val := by intro he; subst i; exact hi j.prop
    simp [eisensteinBalancedPhasedVector,eisensteinDiagonal,eisensteinBalancedHexadVector,
      eisensteinBalancedHexadLift,hij,hz,ternarySignedLift,show (0 : ZMod 3)≠2 by decide]

def eisensteinBalancedBaseFrame (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinBalancedHexadShellVector c j)

theorem eisensteinBalancedFrame_phase (c : TernaryBalancedWords)
    (j : ternarySupport c.val.val) (t : ternaryGolay) :
    eisensteinPhaseIsometries (Multiplicative.ofAdd t) • eisensteinBalancedBaseFrame c j =
      eisensteinBalancedParameterFrame ⟨c,j,eisensteinBalancedPhaseFromCode c t⟩ := by
  rw [eisensteinBalancedBaseFrame,eisensteinFrameAction_vector]
  apply congrArg eisensteinFrameOfVector
  apply Subtype.ext
  apply Subtype.ext
  change (eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t))
    (eisensteinBalancedHexadLatticeVector c j.val)).val =
      eisensteinBalancedPhasedVector c j (eisensteinBalancedPhaseFromCode c t)
  rw [eisensteinIntegralAction_phase]
  exact (eisensteinBalancedPhasedVector_fromCode c j t).symm

theorem eisensteinBalancedFrame_phase_exists (p : EisensteinBalancedParameters) :
    ∃ t : ternaryGolay, eisensteinPhaseIsometries (Multiplicative.ofAdd t) •
      eisensteinBalancedBaseFrame p.1 p.2.1 = eisensteinBalancedParameterFrame p := by
  obtain ⟨t,ht⟩ := ternaryHexadPhase_lift (ternaryBalancedSixWord p.1) p.2.2.val p.2.2.prop
  refine ⟨t,?_⟩
  rw [eisensteinBalancedFrame_phase]
  have he : eisensteinBalancedPhaseFromCode p.1 t=p.2.2 := Subtype.ext (funext ht)
  rw [he]

end Atlas.Conway
