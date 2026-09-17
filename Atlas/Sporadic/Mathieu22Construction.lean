import Atlas.Sporadic.Mathieu22Simple
import Atlas.Mathieu.Mathieu22PairWitt
import Atlas.Mathieu.Mathieu22Choice

noncomputable section
namespace Atlas.Sporadic.Mathieu22
open Atlas.Codes

abbrev PairModel (a : Omega) (b : Mathieu23Points a) := Mathieu22PairModel a b
abbrev PairPoints (a : Omega) (b : Mathieu23Points a) := Mathieu22PairPoints a b

def pairRestriction (a : Omega) (b : Mathieu23Points a) :
    PairModel a b →* Equiv.Perm ({a,b.val} : Set Omega) := mathieu22PairRestriction a b

def pairKernelEquiv (a : Omega) (b : Mathieu23Points a) :
    (pairRestriction a b).ker ≃* Model a b := mathieu22PairKernelEquiv a b

def toPair (a : Omega) (b : Mathieu23Points a) : Model a b →* PairModel a b :=
  mathieu22_to_pair a b

theorem pair_card (a : Omega) (b : Mathieu23Points a) : Nat.card (PairModel a b) = 887040 :=
  mathieu22Pair_order a b

theorem pair_index (a : Omega) (b : Mathieu23Points a) : (pairRestriction a b).ker.index = 2 :=
  mathieu22Pair_kernel_index a b

theorem pair_faithful (a : Omega) (b : Mathieu23Points a) :
    FaithfulSMul (PairModel a b) (PairPoints a b) := mathieu22Pair_faithful a b

def conjugacy {a a' : Omega} {b : Mathieu23Points a} {b' : Mathieu23Points a'}
    {g : Mathieu24CodeModel} (ha : g • a = a') (hb : g • b.val = b'.val) :
    Model a b ≃* Model a' b' := mathieu22ChoiceEquiv ha hb

def conjugacyPoints {a a' : Omega} {b : Mathieu23Points a} {b' : Mathieu23Points a'}
    {g : Mathieu24CodeModel} (ha : g • a = a') (hb : g • b.val = b'.val) :
    Points a b ≃ Points a' b' := mathieu22ChoicePoints ha hb

structure CompleteConstruction (a : Omega) (b : Mathieu23Points a) : Prop where
  finite : Finite (Model a b)
  card : Nat.card (Model a b) = order
  simple : IsSimpleGroup (Model a b)
  noncommuting : ∃ g h : Model a b, g*h ≠ h*g
  degree : Nat.card (Points a b) = 22
  faithful : FaithfulSMul (Model a b) (Points a b)
  three_transitive : MulAction.IsMultiplyPretransitive (Model a b) (Points a b) 3
  not_four_transitive : ¬ MulAction.IsMultiplyPretransitive (Model a b) (Points a b) 4
  embedding_injective : Function.Injective (embedding a b)
  embedding_compatible : (mathieu23_embedding a).comp (toMathieu23 a b) = embedding a b
  block_size : ∀ B ∈ Blocks a b, B.card = 6
  block_count : (Blocks a b).card = 77
  steiner : ∀ T : Finset (Points a b), T.card = 3 → ∃! B, B ∈ Blocks a b ∧ T ⊆ B
  blocks_preserved : ∀ (g : Model a b) B, B ∈ Blocks a b → mathieu22PermuteBlock a b g B ∈ Blocks a b
  pair_card : Nat.card (PairModel a b) = 887040
  pair_restriction_surjective : Function.Surjective (pairRestriction a b)
  pair_kernel_image : (toPair a b).range = (pairRestriction a b).ker
  pair_index : (pairRestriction a b).ker.index = 2
  pair_faithful : FaithfulSMul (PairModel a b) (PairPoints a b)
  pair_blocks_preserved : ∀ (g : PairModel a b) B, B ∈ Blocks a b →
    mathieu22PairPermuteBlock a b g B ∈ Blocks a b
  choice : ∀ (a' : Omega) (b' : Mathieu23Points a'),
    ∃ g : Mathieu24CodeModel, g • a = a' ∧ g • b.val = b'.val

theorem construction_complete (a : Omega) (b : Mathieu23Points a) : CompleteConstruction a b where
  finite := finite a b
  card := card a b
  simple := isSimpleGroup a b
  noncommuting := exists_mul_ne_mul a b
  degree := degree a b
  faithful := faithful a b
  three_transitive := three_transitive a b
  not_four_transitive := not_four_transitive a b
  embedding_injective := embedding_injective a b
  embedding_compatible := embedding_compatible a b
  block_size := mathieu22Blocks_size a b
  block_count := block_count a b
  steiner := steiner a b
  blocks_preserved := mathieu22Blocks_preserved a b
  pair_card := pair_card a b
  pair_restriction_surjective := mathieu22PairRestriction_surjective a b
  pair_kernel_image := mathieu22_to_pair_range a b
  pair_index := pair_index a b
  pair_faithful := pair_faithful a b
  pair_blocks_preserved := mathieu22PairBlocks_preserved a b
  choice := fun a' b' => mathieu22Choice_exists a a' b b'

theorem exists_model (a : Omega) (b : Mathieu23Points a) : ∃ (G : Type) (_ : Group G),
    Nonempty (G ≃* Model a b) ∧ Finite G ∧ Nat.card G = order ∧ IsSimpleGroup G ∧
    (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction a b :=
  ⟨Model a b,inferInstance,⟨MulEquiv.refl _⟩,finite a b,card a b,isSimpleGroup a b,
    exists_mul_ne_mul a b,construction_complete a b⟩

end Atlas.Sporadic.Mathieu22
