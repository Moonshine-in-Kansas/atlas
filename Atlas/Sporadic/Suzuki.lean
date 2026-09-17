import Atlas.Conway.EisensteinOrder
import Atlas.Conway.EisensteinSimplicity
import Atlas.Conway.EisensteinCenter
import Atlas.Conway.EisensteinConwayEmbedding

noncomputable section
namespace Atlas.Sporadic.Suzuki
open Atlas.Algebra Atlas.Codes Atlas.Lattices Atlas.Conway MulAction

/-- The sporadic Suzuki model: the actual Leech centralizer divided by its six
Eisenstein scalar isometries. This namespace is distinct from Lie-type Suzuki groups. -/
abbrev Model := EisensteinProjectiveModel
abbrev LinearCover := eisensteinCentralizer
abbrev HermitianGroup := eisensteinHermitianGroup
abbrev TripleModel := EisensteinTripleModel
abbrev Lattice := EisensteinLattice
abbrev Frames := EisensteinFrame

def baseFrame : Frames := eisensteinStandardFrame

def linearComparison : HermitianGroup ≃* LinearCover := eisensteinCentralizerEquiv

def embedding : LinearCover →* LeechIsometryGroup := eisensteinCentralizer.subtype

def projection : LinearCover →* Model := QuotientGroup.mk' eisensteinCentralizerScalars

def tripleToConway1 : TripleModel →* LeechCentralQuotient := eisensteinTripleToCo1

def tripleProjection : TripleModel →* Model := eisensteinTripleProjection

theorem finite : Finite Model := inferInstance

theorem card : Nat.card Model=448345497600 := eisensteinProjective_order

theorem order : Nat.card Model=2^13*3^7*5^2*7*11*13 := eisensteinProjective_order_factorization

theorem linear_card : Nat.card LinearCover=2690072985600 := eisensteinCentralizer_order

theorem isSimpleGroup : IsSimpleGroup Model := eisensteinProjective_simple

theorem nonabelian : ¬IsMulCommutative Model := eisensteinProjective_nonabelian

theorem exists_mul_ne_mul : ∃ g h : Model,g*h≠h*g := by
  by_contra hn
  push_neg at hn
  exact nonabelian (isMulCommutative_iff.mpr hn)

theorem perfect : Group.IsPerfect Model := eisensteinProjective_perfect

theorem embedding_injective : Function.Injective embedding := Subtype.val_injective

theorem projection_surjective : Function.Surjective projection :=
  QuotientGroup.mk'_surjective _

theorem tripleToConway1_injective : Function.Injective tripleToConway1 :=
  eisensteinTripleToCo1_injective

theorem tripleProjection_surjective : Function.Surjective tripleProjection :=
  eisensteinTripleProjection_surjective

theorem tripleProjection_kernel_card : Nat.card tripleProjection.ker=3 :=
  eisensteinTripleProjection_kernel_card

theorem tripleProjection_kernel_central : tripleProjection.ker ≤ Subgroup.center TripleModel :=
  eisensteinTripleProjection_kernel_central

theorem tripleToConway1_compatible (g : LinearCover) :
    tripleToConway1 (QuotientGroup.mk g)=leechCentralProjection (embedding g) := rfl

theorem center : Subgroup.center LinearCover=eisensteinCentralizerScalars := by
  letI := isSimpleGroup
  exact eisensteinCentralizer_center_of_simple nonabelian

theorem center_card : Nat.card (Subgroup.center LinearCover)=6 := by
  rw [center,eisensteinCentralizerScalars_order]

theorem triple_card : Nat.card TripleModel=1345036492800 := by
  have h := eisensteinCentralizerSigns.card_eq_card_quotient_mul_card_subgroup
  rw [eisensteinCentralizerSigns_card] at h
  change Nat.card LinearCover=Nat.card TripleModel*2 at h
  rw [linear_card] at h
  omega

end Atlas.Sporadic.Suzuki
