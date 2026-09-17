import Atlas.Conway.IcosianSimplicity
import Atlas.Conway.IcosianOrder
import Atlas.Conway.IcosianFullMonomialCentralizer
import Atlas.Conway.IcosianAlternatingConwayProduct

noncomputable section
namespace Atlas.Sporadic.Janko2
open Atlas.Algebra Atlas.Lattices Atlas.Conway

/-- The actual full quaternionic linear Leech group divided by its central signs. -/
abbrev Model := IcosianProjectiveModel
abbrev LinearCover := icosianHermitianGroup
abbrev LeechCentralizer := icosianCentralizer
abbrev RightScalarUnits := icosianNormOneGroup
abbrev Lattice := IcosianLattice
abbrev Points := IcosianRootPoint
abbrev Frames := IcosianRootFrame

def linearComparison : LinearCover ≃* LeechCentralizer := icosianCentralizerEquiv

def embedding : LinearCover →* LeechIsometryGroup := icosianHermitianToCo0

def projection : LinearCover →* Model := icosianProjectiveProjection

def toConway1 : Model →* LeechCentralQuotient := icosianProjectiveToCo1

def rightScalarEmbedding : RightScalarUnits →* LeechIsometryGroup := icosianScalarsToCo0

def scalarAlternatingComparison : IcosianScalarProjectiveModel ≃* alternatingGroup (Fin 5) :=
  icosianScalarProjectiveAlternating

def alternatingProductToConway1 : alternatingGroup (Fin 5) × Model →* LeechCentralQuotient :=
  icosianAlternatingProjectiveToCo1

theorem finite : Finite Model := inferInstance

theorem card : Nat.card Model = 604800 := icosianProjective_order

theorem order : Nat.card Model = 2^7*3^3*5^2*7 := icosianProjective_order_factorization

theorem linear_card : Nat.card LinearCover = 1209600 := icosianHermitian_order

theorem isSimpleGroup : IsSimpleGroup Model := icosianProjective_simple

theorem nonabelian : ¬IsMulCommutative Model := icosianProjective_nonabelian

theorem perfect : Group.IsPerfect Model := icosianProjective_perfect

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := by
  by_contra hn
  push_neg at hn
  exact nonabelian (isMulCommutative_iff.mpr hn)

theorem center : Subgroup.center LinearCover = icosianCentralSigns := icosianHermitian_center

theorem center_card : Nat.card (Subgroup.center LinearCover) = 2 := by
  rw [center,icosianCentralSigns_card]

theorem right_scalar_card : Nat.card RightScalarUnits = 120 := icosianNormOneGroup_card

theorem embedding_injective : Function.Injective embedding := icosianHermitianToCo0_injective

theorem projection_surjective : Function.Surjective projection := icosianProjectiveProjection_surjective

theorem toConway1_injective : Function.Injective toConway1 := icosianProjectiveToCo1_injective

theorem toConway1_compatible (g : LinearCover) :
    toConway1 (projection g) = leechCentralProjection (embedding g) :=
  icosianProjectiveToCo1_mk g

theorem scalar_intersection : rightScalarEmbedding.range ⊓ icosianCentralizer = leechCentralSigns :=
  icosianScalars_inf_centralizer

theorem scalar_commutation (u : RightScalarUnits) (g : LinearCover) :
    Commute (rightScalarEmbedding u) (embedding g) := icosianScalars_commute_Hermitian u g

theorem central_product_kernel (u : RightScalarUnits) (g : LinearCover) :
    (u,g) ∈ icosianScalarCentralProduct.ker ↔
      (u=1 ∧ g=1) ∨ (u=icosianNormOneMinusOne ∧ g=icosianCentralSign) :=
  icosianScalarCentralProduct_kernel_iff u g

theorem central_product_injective : Function.Injective icosianCentralProductToCo0 :=
  icosianCentralProductToCo0_injective

theorem alternatingProductToConway1_injective : Function.Injective alternatingProductToConway1 :=
  icosianAlternatingProjectiveToCo1_injective

end Atlas.Sporadic.Janko2
