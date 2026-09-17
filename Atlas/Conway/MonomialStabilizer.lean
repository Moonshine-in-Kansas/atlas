import Atlas.Conway.CrossStabilizerShape
import Atlas.Conway.SignedPermutationRecovery
import Atlas.Conway.MonomialOrder

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def standardCrossStabilizer : Subgroup LeechIsometryGroup :=
  (MulAction.stabilizer (Equiv.Perm LeechCross) standardCross).comap crossRepresentation

theorem standardCrossStabilizer_mem (g : LeechIsometryGroup) :
    g ∈ standardCrossStabilizer ↔ crossAction g standardCross = standardCross := Iff.rfl

theorem standardCross_parameters (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) :
    standardCrossSignWord g hg ∈ golay ∧ CodePreserving (standardCrossCoordinatePermutation g hg) := by
  apply signedPermutation_parameters
  intro x
  have he : signChange (standardCrossSignWord g hg)
      (integerPermutation (standardCrossCoordinatePermutation g hg) x.val) = (g.val x).val := by
    ext i
    exact (standardCross_signed_shape g hg x i).symm
  rw [he]
  exact (g.val x).prop

def recoverMonomial (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) : GolayMonomialGroup :=
  ⟨Multiplicative.ofAdd ⟨standardCrossSignWord g hg,(standardCross_parameters g hg).1⟩,
    ⟨standardCrossCoordinatePermutation g hg,(standardCross_parameters g hg).2⟩⟩

theorem recoverMonomial_spec (g : LeechIsometryGroup)
    (hg : crossAction g standardCross = standardCross) : monomialEmbedding (recoverMonomial g hg) = g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  ext i
  exact (standardCross_signed_shape g hg x i).symm

theorem recoverMonomial_embedding (m : GolayMonomialGroup) :
    recoverMonomial (monomialEmbedding m) (monomial_fixes_standardCross m) = m := by
  apply monomialEmbedding_injective
  exact recoverMonomial_spec _ _

theorem standardCrossStabilizer_eq_monomial : standardCrossStabilizer = monomialSubgroup := by
  ext g
  constructor
  · intro hg
    exact ⟨recoverMonomial g hg,recoverMonomial_spec g hg⟩
  · rintro ⟨m,rfl⟩
    exact monomial_fixes_standardCross m

def standardCrossStabilizerEquiv : standardCrossStabilizer ≃* GolayMonomialGroup :=
  (MulEquiv.subgroupCongr standardCrossStabilizer_eq_monomial).trans monomialSubgroupEquiv.symm

theorem standardCrossStabilizerEquiv_compatible (g : standardCrossStabilizer) :
    monomialEmbedding (standardCrossStabilizerEquiv g) = g.val := by
  exact congrArg Subtype.val (monomialSubgroupEquiv.apply_symm_apply
    ((MulEquiv.subgroupCongr standardCrossStabilizer_eq_monomial) g))

theorem standardCrossStabilizer_order : Nat.card standardCrossStabilizer = 1002795171840 := by
  rw [Nat.card_congr (MulEquiv.subgroupCongr standardCrossStabilizer_eq_monomial).toEquiv]
  exact monomial_order

structure MonomialStabilizerConstruction : Prop where
  full_stabilizer : standardCrossStabilizer = monomialSubgroup
  order : Nat.card standardCrossStabilizer = 1002795171840
  recovery : ∀ g hg, monomialEmbedding (recoverMonomial g hg) = g
  inverse_recovery : ∀ m, recoverMonomial (monomialEmbedding m) (monomial_fixes_standardCross m) = m
  compatibility : ∀ g, monomialEmbedding (standardCrossStabilizerEquiv g) = g.val

theorem monomial_stabilizer_constructed : MonomialStabilizerConstruction where
  full_stabilizer := standardCrossStabilizer_eq_monomial
  order := standardCrossStabilizer_order
  recovery := recoverMonomial_spec
  inverse_recovery := recoverMonomial_embedding
  compatibility := standardCrossStabilizerEquiv_compatible

end Atlas.Conway
