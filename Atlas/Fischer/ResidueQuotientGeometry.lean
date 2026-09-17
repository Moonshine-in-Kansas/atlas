import Atlas.Fischer.ResidueFaithfulAction
import Atlas.Fischer.ResiduePointTransport
import Atlas.Fischer.ResidueTransitivity

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Transitivity descends to the actual central quotient on the original points. -/
theorem residueGroup_transitive (S : Finset Omega) (hS : S.card ≤ 4) :
    MulAction.IsPretransitive (ResidueGroup S) (ResiduePoint S) := by
  haveI := residuePoint_transitive S hS
  constructor
  intro x y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (residueCentralizer S) x y
  refine ⟨QuotientGroup.mk g,?_⟩
  exact hg

/-- Choice transport is compatible with the quotient action on original points. -/
theorem residueQuotientTransport_equivariant (S T : Finset Omega) (g : rootGeneratedRayGroup)
    (h : (MulAut.conj g) '' residueBasicSet S = residueBasicSet T)
    (a : ResidueGroup S) (x : ResiduePoint S) :
    residuePointTransport S T g h (a • x) =
      residueQuotientTransport S T g h a • residuePointTransport S T g h x := by
  obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective a
  exact residuePointTransport_equivariant S T g h b x

end Atlas.Fischer
