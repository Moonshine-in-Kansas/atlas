import Atlas.Conway.IcosianLocalDReductionNecessity

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices Atlas.Codes

def icosianLocalDStabilizer : Subgroup icosianLiftedMonomial :=
  (MulAction.stabilizer icosianHermitianGroup (icosianRootPoint icosianLocalDRoot)).comap
    icosianMonomialToHermitian

def icosianLocalDStabilizerScalar (g : icosianLocalDStabilizer) : icosianNormOneGroup :=
  ((icosianMonomial_line_iff g.val icosianLocalDRoot).mp g.property).choose

theorem icosianLocalDStabilizerScalar_spec (g : icosianLocalDStabilizer) :
    ∀ i,(g.val.val.left i).val.val*(icosianLocalDRoot.val (g.val.val.right.symm i)).val=
      (icosianLocalDRoot.val i).val*(icosianLocalDStabilizerScalar g).val.val :=
  ((icosianMonomial_line_iff g.val icosianLocalDRoot).mp g.property).choose_spec

def icosianLocalDStabilizerParameter (g : icosianLocalDStabilizer) : IcosianLocalDUnitParameters :=
  ⟨icosianLocalDStabilizerScalar g,
    icosianLocalDLine_reduction_test g.val (icosianLocalDLine_permutation g.val g.property)
      (icosianLocalDStabilizerScalar g) (icosianLocalDStabilizerScalar_spec g)⟩

theorem icosianLocalDStabilizerParameter_injective :
    Function.Injective icosianLocalDStabilizerParameter := by
  intro g h he
  have hp : g.val.val.right=h.val.val.right :=
    (icosianLocalDLine_permutation g.val g.property).trans
      (icosianLocalDLine_permutation h.val h.property).symm
  have hu : icosianLocalDStabilizerScalar g=icosianLocalDStabilizerScalar h :=
    congrArg (fun p : IcosianLocalDUnitParameters => p.val) he
  apply Subtype.ext
  apply icosianMonomial_line_determined icosianLocalDRoot icosianLocalDRoot_nonzero
    g.val h.val hp (icosianLocalDStabilizerScalar g) (icosianLocalDStabilizerScalar_spec g)
  rw [hu]
  exact icosianLocalDStabilizerScalar_spec h

theorem icosianLocalDStabilizer_card_le : Nat.card icosianLocalDStabilizer≤24 := by
  have h := Nat.card_le_card_of_injective icosianLocalDStabilizerParameter
    icosianLocalDStabilizerParameter_injective
  rwa [icosianLocalDUnitParameters_card] at h

end Atlas.Conway
