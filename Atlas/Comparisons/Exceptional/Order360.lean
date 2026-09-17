import Atlas.Comparisons.Exceptional.PSL2NineAction
import Atlas.Comparisons.Exceptional.BinaryDerived
import Atlas.GroupTheory.FiniteGeneratorActionComparison

/-! The faithful projective-line action and the faithful action on complementary
triples have the same generator images. This identifies the actual groups;
no abstract uniqueness theorem for simple groups of order 360 is assumed. -/
noncomputable section
namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups

private theorem nine_generator_images : ∀ g ∈ Nine.generators,
    Nine.permutation g ∈ TriplePartitions.action.range := by
  intro g hg
  rcases hg with rfl | hg
  · exact ⟨TriplePartitions.firstCycle,
      TriplePartitions.action_firstCycle.trans Nine.permutation_upper.symm⟩
  rcases hg with rfl | hg
  · exact ⟨TriplePartitions.secondCycle,
      TriplePartitions.action_secondCycle.trans Nine.permutation_omega.symm⟩
  have he : g = (Nine.inversionMatrix : PSL(2, Nine.F)) := Set.mem_singleton_iff.mp hg
  subst g
  exact ⟨TriplePartitions.doubleSwap,
    TriplePartitions.action_doubleSwap.trans Nine.permutation_inversion.symm⟩

theorem psl2Card9_card {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 9) :
    Nat.card PSL(2,K) = 360 := by
  rw [Atlas.card_psl_factor (F := K) 2, hK]
  norm_num [Finset.prod_Icc_succ_top]

theorem alt6_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The common intrinsic ten-point actions identify the two actual models. -/
def psl2NineCoordinatesEquivAlt6 : PSL(2, Nine.F) ≃* alternatingGroup (Fin 6) :=
  Atlas.GroupTheory.equivOfGeneratorActions Nine.permutation TriplePartitions.action
    Nine.permutation_injective TriplePartitions.action_injective
    ((psl2Card9_card Nine.card).trans alt6_card.symm)
    Nine.generators Nine.psl_generated nine_generator_images

theorem psl2NineCoordinatesEquivAlt6_action (g : PSL(2, Nine.F)) :
    TriplePartitions.action (psl2NineCoordinatesEquivAlt6 g) = Nine.permutation g :=
  Atlas.GroupTheory.equivOfGeneratorActions_coherence _ _ _ _ _ _ _ _ g

/-- Field transport makes the exceptional comparison uniform in the field model. -/
def psl2Card9EquivAlt6 {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 9) :
    PSL(2,K) ≃* alternatingGroup (Fin 6) :=
  (Atlas.fieldEquivPSL 2 (Nine.fieldEquiv hK)).trans psl2NineCoordinatesEquivAlt6

/-- The existing canonical finite-field endpoint. -/
def psl2NineEquivAlt6 : PSL(2,GaloisField 3 2) ≃* alternatingGroup (Fin 6) :=
  psl2Card9EquivAlt6 (by rw [GaloisField.card 3 2 (by decide)]; norm_num)

def psl2Card9EquivB2BinaryDerived {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 9) :
    PSL(2,K) ≃* commutator (Atlas.Orthogonal.ProjectiveElementary
      (Atlas.Orthogonal.formB 2 (ZMod 2))) :=
  (psl2Card9EquivAlt6 hK).trans Atlas.Orthogonal.b2BinaryDerivedEquivAlternating.symm

def psl2Card9EquivC2BinaryDerived {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 9) :
    PSL(2,K) ≃* commutator (Atlas.Symplectic.PSp 2 (ZMod 2)) :=
  (psl2Card9EquivAlt6 hK).trans c2BinaryDerivedEquivAlt6.symm

end Atlas.Comparisons.Exceptional
