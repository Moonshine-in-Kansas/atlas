import Atlas.Lattices.LeechClassTypes

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

structure IntrinsicCrossConstruction : Prop where
  quadratic_space : ModTwoQuadraticConstruction
  class_counts : (shellClasses 4).card = 98280 ∧ (shellClasses 6).card = 8386560 ∧
    (shellClasses 8).card = 8292375
  classes_exhaustive : shortClasses = Finset.univ
  intrinsic_class : ∀ a, MinimumEightClass a ↔ a ∈ shellClasses 8
  crosses_count : Nat.card LeechCross = 8292375
  vectors_count : ∀ c, (crossVectors c).card = 48
  pairs_count : ∀ c : LeechCross, (normEightPairs c.val).card = 24
  orthogonal : ∀ c x y, x ∈ crossVectors c → y ∈ crossVectors c → x ≠ y → x ≠ -y →
    rationalForm (rationalEmbedding x.val) (rationalEmbedding y.val) = 0
  spans : ∀ c, Submodule.span ℚ (Set.range (crossRepresentativeVector c)) = ⊤
  transports : ∀ g c, (crossVectors c).image g.val = crossVectors (crossAction g c)
  standard : crossIntegerVectors standardCross = axisEightVectors
  type_quadratic : ∀ a, leechQuadratic a = (leechClassType a : Bit)

theorem leech_intrinsic_crosses_constructed : IntrinsicCrossConstruction where
  quadratic_space := leech_mod_two_quadratic_constructed
  class_counts := shellClasses_counts
  classes_exhaustive := shortClasses_eq_univ
  intrinsic_class := minimumEightClass_iff
  crosses_count := leechCross_card
  vectors_count := crossVectors_card
  pairs_count := crossPairs_card
  orthogonal := crossVectors_orthogonal
  spans := crossRepresentatives_span
  transports := crossVectors_transport
  standard := standardCross_vectors
  type_quadratic := leechQuadratic_classType

end Atlas.Lattices
