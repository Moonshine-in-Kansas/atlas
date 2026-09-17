import Atlas.Sporadic.Mathieu23
import Atlas.Mathieu.Mathieu23Order
import Atlas.Mathieu.Mathieu23Witt

noncomputable section
namespace Atlas.Sporadic.Mathieu23
local instance (a : Atlas.Codes.Omega) : Fintype (Points a) := Fintype.ofFinite _

abbrev PuncturedCode (a : Atlas.Codes.Omega) := Atlas.Codes.puncturedGolay a
abbrev Blocks (a : Atlas.Codes.Omega) := Atlas.Codes.mathieu23Blocks a

theorem card_factorization (a : Atlas.Codes.Omega) :
    Nat.card (Model a) = 2^7 * 3^2 * 5 * 7 * 11 * 23 :=
  Atlas.Codes.mathieu23_order_factorization a

theorem index_product (a : Atlas.Codes.Omega) :
    24 * Nat.card (Model a) = Nat.card Atlas.Codes.Mathieu24CodeModel :=
  Atlas.Codes.mathieu23_index_product a

theorem not_five_transitive (a : Atlas.Codes.Omega) :
    ¬ MulAction.IsMultiplyPretransitive (Model a) (Points a) 5 :=
  Atlas.Codes.mathieu23_not_five_transitive a

def puncturedCodeAutEquiv (a : Atlas.Codes.Omega) :
    Model a ≃* Atlas.Codes.puncturedCodeAutomorphisms a := Atlas.Codes.puncturedGolayAutEquiv a

structure CompleteConstruction (a : Atlas.Codes.Omega) : Prop where
  group : Construction a
  not_five_transitive : ¬ MulAction.IsMultiplyPretransitive (Model a) (Points a) 5
  code_dimension : Module.finrank Atlas.Codes.Bit (PuncturedCode a) = 12
  code_card : Nat.card (PuncturedCode a) = 4096
  code_minimum : ∀ w ∈ PuncturedCode a, w ≠ 0 → 7 ≤ hammingNorm w
  code_minimum_witness : ∃ w ∈ PuncturedCode a, hammingNorm w = 7
  code_full_aut : Nonempty (Model a ≃* Atlas.Codes.puncturedCodeAutomorphisms a)
  block_size : ∀ B ∈ Blocks a, B.card = 7
  block_count : (Blocks a).card = 253
  steiner : ∀ T : Finset (Points a), T.card = 4 → ∃! B, B ∈ Blocks a ∧ T ⊆ B
  blocks_preserved : ∀ (g : Model a) B, B ∈ Blocks a →
    Atlas.Codes.mathieu23PermuteBlock a g B ∈ Blocks a

theorem construction_complete (a : Atlas.Codes.Omega) : CompleteConstruction a where
  group := construction a
  not_five_transitive := not_five_transitive a
  code_dimension := Atlas.Codes.puncturedGolay_finrank a
  code_card := Atlas.Codes.puncturedGolay_card a
  code_minimum := Atlas.Codes.puncturedGolay_minimum a
  code_minimum_witness := Atlas.Codes.puncturedGolay_minimum_witness a
  code_full_aut := ⟨puncturedCodeAutEquiv a⟩
  block_size := Atlas.Codes.mathieu23Blocks_size a
  block_count := Atlas.Codes.mathieu23Blocks_card a
  steiner := Atlas.Codes.mathieu23_steiner a
  blocks_preserved := Atlas.Codes.mathieu23Blocks_preserved a

theorem exists_model (a : Atlas.Codes.Omega) : ∃ (G : Type) (_ : Group G),
    Nonempty (G ≃* Model a) ∧ Finite G ∧ Nat.card G = order ∧ IsSimpleGroup G ∧
    (∃ g h : G, g * h ≠ h * g) ∧ CompleteConstruction a :=
  ⟨Model a, inferInstance, ⟨MulEquiv.refl _⟩, finite a, card a, isSimpleGroup a,
    exists_mul_ne_mul a, construction_complete a⟩

end Atlas.Sporadic.Mathieu23
