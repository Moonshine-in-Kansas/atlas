import Atlas.Mathieu.Mathieu11Simplicity
import Atlas.Mathieu.Mathieu11PointOrders
import Atlas.Mathieu.Mathieu11ChoiceWitt
import Atlas.Sporadic.Mathieu12

noncomputable section
namespace Atlas.Sporadic.Mathieu11
open Atlas.Codes

abbrev Model (D : Dodecad) (a : Mathieu12Points D) := ↥(Mathieu11PointModel D a)
abbrev Points (D : Dodecad) (a : Mathieu12Points D) := Mathieu11Points D a
abbrev Blocks (D : Dodecad) (a : Mathieu12Points D) := mathieu11Blocks D a
def order : ℕ := 7920

theorem finite (D : Dodecad) (a : Mathieu12Points D) : Finite (Model D a) := inferInstance
theorem card (D : Dodecad) (a : Mathieu12Points D) : Nat.card (Model D a) = order := mathieu11_order D a
theorem card_factorization (D : Dodecad) (a : Mathieu12Points D) :
    Nat.card (Model D a) = 2^4 * 3^2 * 5 * 11 := mathieu11_order_factorization D a
theorem isSimpleGroup (D : Dodecad) (a : Mathieu12Points D) : IsSimpleGroup (Model D a) := mathieu11_simple D a
theorem exists_mul_ne_mul (D : Dodecad) (a : Mathieu12Points D) :
    ∃ g h : Model D a, g*h ≠ h*g := mathieu11_noncommuting_pair D a

def embedding (D : Dodecad) (a : Mathieu12Points D) : Model D a →* Mathieu24CodeModel := mathieu11_to_m24 D a
def toMathieu12 (D : Dodecad) (a : Mathieu12Points D) : Model D a →* Mathieu12DodecadModel D := mathieu11_embedding D a
def toMathieu23 (D : Dodecad) (a : Mathieu12Points D) : Model D a →* Mathieu23PointModel a.val := mathieu11_to_m23 D a

theorem embedding_injective (D : Dodecad) (a : Mathieu12Points D) :
    Function.Injective (embedding D a) := mathieu11_to_m24_injective D a
theorem embeddings_compatible (D : Dodecad) (a : Mathieu12Points D) :
    (mathieu23_embedding a.val).comp (toMathieu23 D a) = (mathieu12_embedding D).comp (toMathieu12 D a) :=
  mathieu11_embeddings_commute D a
theorem image_intersection (D : Dodecad) (a : Mathieu12Points D) :
    (embedding D a).range = Mathieu12DodecadModel D ⊓ Mathieu23PointModel a.val := mathieu11_image_intersection D a

theorem degree (D : Dodecad) (a : Mathieu12Points D) : Nat.card (Points D a) = 11 := mathieu11_degree D a
theorem faithful (D : Dodecad) (a : Mathieu12Points D) : FaithfulSMul (Model D a) (Points D a) := mathieu11_faithful D a
theorem sharp_four_transitive (D : Dodecad) (a : Mathieu12Points D) (e f : Fin 4 ↪ Points D a) :
    ∃! g : Model D a, g • e = f := mathieu11_sharp_four_transitive D a e f
theorem not_five_transitive (D : Dodecad) (a : Mathieu12Points D) :
    ¬ MulAction.IsMultiplyPretransitive (Model D a) (Points D a) 5 := mathieu11_not_five_transitive D a

theorem block_count (D : Dodecad) (a : Mathieu12Points D) : (Blocks D a).card = 66 := mathieu11Blocks_card D a
theorem steiner (D : Dodecad) (a : Mathieu12Points D) (T : Finset (Points D a)) (hT : T.card = 4) :
    ∃! B, B ∈ Blocks D a ∧ T ⊆ B := mathieu11_steiner D a T hT

def conjugacy {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val) : Model D a ≃* Model E b :=
  mathieu11ChoiceEquiv hg ha

def conjugacyPoints {D E : Dodecad} {a : Mathieu12Points D} {b : Mathieu12Points E}
    {g : Mathieu24CodeModel} (hg : g • D = E) (ha : g.val a.val = b.val) : Points D a ≃ Points E b :=
  mathieu11ChoicePoints hg ha

abbrev StandardModel := Model Mathieu12.standardDodecad Mathieu12.standardPoint

structure CompleteConstruction (D : Dodecad) (a : Mathieu12Points D) : Prop where
  finite : Finite (Model D a)
  card : Nat.card (Model D a) = order
  simple : IsSimpleGroup (Model D a)
  noncommuting : ∃ g h : Model D a, g*h ≠ h*g
  degree : Nat.card (Points D a) = 11
  faithful : FaithfulSMul (Model D a) (Points D a)
  sharp_four : ∀ e f : Fin 4 ↪ Points D a, ∃! g : Model D a, g • e = f
  not_five : ¬ MulAction.IsMultiplyPretransitive (Model D a) (Points D a) 5
  embedding_injective : Function.Injective (embedding D a)
  toM12_injective : Function.Injective (toMathieu12 D a)
  toM23_injective : Function.Injective (toMathieu23 D a)
  embeddings_compatible : (mathieu23_embedding a.val).comp (toMathieu23 D a) =
    (mathieu12_embedding D).comp (toMathieu12 D a)
  image_intersection : (embedding D a).range = Mathieu12DodecadModel D ⊓ Mathieu23PointModel a.val
  block_size : ∀ B ∈ Blocks D a, B.card = 5
  block_count : (Blocks D a).card = 66
  steiner : ∀ T : Finset (Points D a), T.card = 4 → ∃! B, B ∈ Blocks D a ∧ T ⊆ B
  blocks_preserved : ∀ g B, B ∈ Blocks D a → mathieu11PermuteBlock D a g B ∈ Blocks D a
  octad_recovery : ∀ B ∈ Blocks D a, ∃! O : Finset Omega,
    O ∈ octads ∧ mathieu12OctadTrace D O = insert a (mathieu11BlockLift D a B)
  choice : ∀ (E : Dodecad) (b : Mathieu12Points E),
    ∃ g : Mathieu24CodeModel, g • D = E ∧ g.val a.val = b.val

theorem construction_complete (D : Dodecad) (a : Mathieu12Points D) : CompleteConstruction D a where
  finite := finite D a
  card := card D a
  simple := isSimpleGroup D a
  noncommuting := exists_mul_ne_mul D a
  degree := degree D a
  faithful := faithful D a
  sharp_four := sharp_four_transitive D a
  not_five := not_five_transitive D a
  embedding_injective := embedding_injective D a
  toM12_injective := mathieu11_embedding_injective D a
  toM23_injective := mathieu11_to_m23_injective D a
  embeddings_compatible := embeddings_compatible D a
  image_intersection := image_intersection D a
  block_size := mathieu11Blocks_size D a
  block_count := block_count D a
  steiner := steiner D a
  blocks_preserved := mathieu11Blocks_preserved D a
  octad_recovery := mathieu11Blocks_octad_recovery D a
  choice := fun E b => dodecad_point_flags_transitive D E a b

theorem exists_model (D : Dodecad) (a : Mathieu12Points D) : ∃ (G : Type) (_ : Group G),
    Nonempty (G ≃* Model D a) ∧ Finite G ∧ Nat.card G = order ∧ IsSimpleGroup G ∧
    (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction D a :=
  ⟨Model D a,inferInstance,⟨MulEquiv.refl _⟩,finite D a,card D a,isSimpleGroup D a,
    exists_mul_ne_mul D a,construction_complete D a⟩

end Atlas.Sporadic.Mathieu11
