import Atlas.Mathieu.Mathieu22Witt

noncomputable section
namespace Atlas.Sporadic.Mathieu22

abbrev Model (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :=
  ↥(Atlas.Codes.Mathieu22PointModel a b)
abbrev Points (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :=
  Atlas.Codes.Mathieu22Points a b
abbrev Blocks (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :=
  Atlas.Codes.mathieu22Blocks a b

def order : ℕ := 443520

theorem finite (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    Finite (Model a b) := inferInstance

theorem card (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    Nat.card (Model a b) = order := Atlas.Codes.mathieu22_order a b

theorem card_factorization (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    Nat.card (Model a b) = 2^7 * 3^2 * 5 * 7 * 11 := Atlas.Codes.mathieu22_order_factorization a b

def embedding (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    Model a b →* Atlas.Codes.Mathieu24CodeModel := Atlas.Codes.mathieu22_embedding a b

def toMathieu23 (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    Model a b →* Atlas.Codes.Mathieu23PointModel a := Atlas.Codes.mathieu22_to_mathieu23 a b

theorem embedding_injective (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    Function.Injective (embedding a b) := Atlas.Codes.mathieu22_embedding_injective a b

theorem embedding_compatible (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    (Atlas.Codes.mathieu23_embedding a).comp (toMathieu23 a b) = embedding a b := rfl

theorem degree (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    Nat.card (Points a b) = 22 := Atlas.Codes.mathieu22_degree a b

theorem faithful (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    FaithfulSMul (Model a b) (Points a b) := Atlas.Codes.mathieu22_faithful a b

theorem three_transitive (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    MulAction.IsMultiplyPretransitive (Model a b) (Points a b) 3 := Atlas.Codes.mathieu22_three_transitive a b

theorem not_four_transitive (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    ¬ MulAction.IsMultiplyPretransitive (Model a b) (Points a b) 4 := Atlas.Codes.mathieu22_not_four_transitive a b

theorem exists_mul_ne_mul (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    ∃ g h : Model a b, g * h ≠ h * g := Atlas.Codes.mathieu22_noncommuting_pair a b

theorem block_count (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a) :
    (Blocks a b).card = 77 := Atlas.Codes.mathieu22Blocks_card a b

theorem steiner (a : Atlas.Codes.Omega) (b : Atlas.Codes.Mathieu23Points a)
    (T : Finset (Points a b)) (hT : T.card = 3) :
    ∃! B, B ∈ Blocks a b ∧ T ⊆ B := Atlas.Codes.mathieu22_steiner a b T hT

end Atlas.Sporadic.Mathieu22
