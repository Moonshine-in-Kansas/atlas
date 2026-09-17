import Atlas.Sporadic.Conway2Simplicity
import Atlas.Conway.LeechOrthogonalComplement
import Atlas.Lattices.LeechConstruction

noncomputable section
namespace Atlas.Sporadic.Conway2
open Atlas.Codes Atlas.Lattices Atlas.Conway
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

abbrev Complement := leechOrthogonalComplement vector.val

theorem vector_norm : integerDot vector.val.val vector.val.val = 32 := vector.prop

theorem complement_rank : Module.finrank ℤ Complement = 23 :=
  leechOrthogonalComplement_rank vector.val (by rw [vector_norm]; decide)

theorem complement_free : Module.Free ℤ Complement := inferInstance

theorem complement_finite : Module.Finite ℤ Complement := inferInstance

def integralRepresentation : Model →* (Complement ≃ₗ[ℤ] Complement) :=
  leechComplementRepresentation vector.val

theorem integralRepresentation_injective : Function.Injective integralRepresentation :=
  leechComplementRepresentation_injective vector.val (by rw [vector_norm]; decide)

theorem integralRepresentation_preserves (g : Model) (x y : Complement) :
    integerDot (integralRepresentation g x).val.val (integralRepresentation g y).val.val =
      integerDot x.val.val y.val.val := leechComplementRepresentation_preserves vector.val g x y

theorem embedding_injective : Function.Injective embedding := Subtype.val_injective

theorem antipodalStabilizerEquiv_compatible (g : Model) :
    (antipodalStabilizerEquiv g).val = toConway1 g := rfl

theorem signs_nontrivial : Nontrivial signs := by
  letI : Fintype signs := Fintype.ofFinite _
  apply Fintype.one_lt_card_iff_nontrivial.mp
  rw [← Nat.card_eq_fintype_card,signs_card]
  decide

theorem local_maximal : IsCoatom LocalGroup := by
  have := primitive
  have := transitive
  have : Nontrivial Points := by
    letI : Fintype Points := Fintype.ofFinite _
    apply Fintype.one_lt_card_iff_nontrivial.mp
    rw [← Nat.card_eq_fintype_card,degree]
    decide
  rw [← full_point_stabilizer]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive Model basePoint

structure CompleteConstruction : Prop where
  lattice : LeechConstruction
  norm : integerDot vector.val.val vector.val.val = 32
  finite : Finite Model
  card : Nat.card Model = order
  factorization : Nat.card Model = 2^18 * 3^6 * 5^3 * 7 * 11 * 23
  simple : IsSimpleGroup Model
  noncommuting : ∃ g h : Model, g*h ≠ h*g
  perfect : Group.IsPerfect Model
  cover_injective : Function.Injective embedding
  quotient_injective : Function.Injective toConway1
  quotient_compatible : ∀ g, (antipodalStabilizerEquiv g).val = toConway1 g
  shell_index : 196560 * Nat.card Model = Nat.card LeechIsometryGroup
  line_index : 98280 * Nat.card Model = Nat.card LeechCentralQuotient
  degree : Nat.card Points = 46575
  faithful : FaithfulSMul Model Points
  transitive : MulAction.IsPretransitive Model Points
  primitive : MulAction.IsPreprimitive Model Points
  local_full : MulAction.stabilizer Model basePoint = LocalGroup
  local_order : Nat.card LocalGroup = 908328960
  local_maximal : IsCoatom LocalGroup
  sign_order : Nat.card signs = 1024
  signs_nontrivial : Nontrivial signs
  sign_rank : Module.finrank Bit SignModule = 10
  signs_normal : signs.Normal
  signs_commute : ∀ g h : signs, g*h = h*g
  local_kernel : pairProjection.ker = signs
  local_section : ∀ q, pairProjection (pairSection q) = q
  outer_section : ∀ p, outerPairRestriction (outerPairSection p) = p
  subdegrees : ∀ t : Fin 5,
    Nat.card {l : Points // suborbitIndex l = t} = ![1,462,21120,2464,22528] t
  suborbit_transitive : ∀ l m : Points, suborbitIndex l = suborbitIndex m →
    ∃ g : MulAction.stabilizer Model basePoint, g • l = m
  signs_generate : Subgroup.normalClosure (embeddedSigns : Set Model) = ⊤
  complement_rank : Module.finrank ℤ Complement = 23
  complement_free : Module.Free ℤ Complement
  complement_finite : Module.Finite ℤ Complement
  integral_faithful : Function.Injective integralRepresentation
  integral_isometric : ∀ g x y,
    integerDot (integralRepresentation g x).val.val (integralRepresentation g y).val.val =
      integerDot x.val.val y.val.val

theorem construction : CompleteConstruction where
  lattice := leech_constructed
  norm := vector_norm
  finite := finite
  card := card
  factorization := card_factorization
  simple := isSimpleGroup
  noncommuting := exists_mul_ne_mul
  perfect := perfect
  cover_injective := embedding_injective
  quotient_injective := toConway1_injective
  quotient_compatible := antipodalStabilizerEquiv_compatible
  shell_index := shell_index_product
  line_index := line_index_product
  degree := degree
  faithful := faithful
  transitive := transitive
  primitive := primitive
  local_full := full_point_stabilizer
  local_order := local_card
  local_maximal := local_maximal
  sign_order := signs_card
  signs_nontrivial := signs_nontrivial
  sign_rank := signModule_rank
  signs_normal := signs_normal
  signs_commute := signs_commute
  local_kernel := pairProjection_kernel
  local_section := pairProjection_section
  outer_section := outerPairSection_rightInverse
  subdegrees := suborbit_card
  suborbit_transitive := suborbit_transitive
  signs_generate := signs_normalClosure
  complement_rank := complement_rank
  complement_free := complement_free
  complement_finite := complement_finite
  integral_faithful := integralRepresentation_injective
  integral_isometric := integralRepresentation_preserves

theorem construction_complete : CompleteConstruction := construction

theorem exists_model : ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model) ∧
    Finite G ∧ Nat.card G = order ∧ IsSimpleGroup G ∧
    (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction :=
  ⟨Model,inferInstance,⟨MulEquiv.refl _⟩,finite,card,isSimpleGroup,exists_mul_ne_mul,construction⟩

end Atlas.Sporadic.Conway2
