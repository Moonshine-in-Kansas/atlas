import Atlas.Mathieu.Mathieu12Simplicity
import Atlas.Mathieu.Mathieu12Choice
import Atlas.Mathieu.DodecadPair
import Atlas.Mathieu.Mathieu11Embeddings

noncomputable section
namespace Atlas.Sporadic.Mathieu12
open Atlas.Codes

abbrev Model (D : Dodecad) := ↥(Mathieu12DodecadModel D)
abbrev Points (D : Dodecad) := Mathieu12Points D
abbrev Blocks (D : Dodecad) := mathieu12Blocks D
abbrev PairModel (D : Dodecad) := ↥(Mathieu12PairModel D)
def order : ℕ := 95040

theorem finite (D : Dodecad) : Finite (Model D) := inferInstance
theorem card (D : Dodecad) : Nat.card (Model D) = order := mathieu12_order D
theorem card_factorization (D : Dodecad) : Nat.card (Model D) = 2^6 * 3^3 * 5 * 11 :=
  mathieu12_order_factorization D
theorem isSimpleGroup (D : Dodecad) : IsSimpleGroup (Model D) := mathieu12_simple D
theorem exists_mul_ne_mul (D : Dodecad) : ∃ g h : Model D, g*h ≠ h*g := mathieu12_noncommuting_pair D

def embedding (D : Dodecad) : Model D →* Mathieu24CodeModel := mathieu12_embedding D
theorem embedding_injective (D : Dodecad) : Function.Injective (embedding D) := mathieu12_embedding_injective D
theorem degree (D : Dodecad) : Nat.card (Points D) = 12 := mathieu12_degree D
theorem faithful (D : Dodecad) : FaithfulSMul (Model D) (Points D) := mathieu12_faithful D
theorem sharp_five_transitive (D : Dodecad) (e f : Fin 5 ↪ Points D) :
    ∃! g : Model D, g • e = f := mathieu12_sharp_five_transitive D e f
theorem not_six_transitive (D : Dodecad) : ¬ MulAction.IsMultiplyPretransitive (Model D) (Points D) 6 :=
  mathieu12_not_six_transitive D

theorem block_count (D : Dodecad) : (Blocks D).card = 132 := mathieu12Blocks_card D
theorem steiner (D : Dodecad) (T : Finset (Points D)) (hT : T.card = 5) :
    ∃! B, B ∈ Blocks D ∧ T ⊆ B := mathieu12_steiner D T hT

def toPair (D : Dodecad) : Model D →* PairModel D := mathieu12_to_pair D
def pairRestriction (D : Dodecad) : PairModel D →* Equiv.Perm ({D,dodecadComplement D} : Set Dodecad) :=
  mathieu12PairRestriction D
def pairKernelEquiv (D : Dodecad) : (pairRestriction D).ker ≃* Model D := mathieu12PairKernelEquiv D

def conjugacy {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E) : Model D ≃* Model E :=
  mathieu12ChoiceEquiv hg
def conjugacyPoints {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E) : Points D ≃ Points E :=
  mathieu12ChoicePoints hg

def markedCoordinate : Omega := ((0,0),0)
def standardDodecad : Dodecad := Classical.choose (dodecad_through_coordinate markedCoordinate)
theorem standardDodecad_marked : markedCoordinate ∈ standardDodecad.val :=
  Classical.choose_spec (dodecad_through_coordinate markedCoordinate)
def standardPoint : Points standardDodecad := ⟨markedCoordinate,standardDodecad_marked⟩
abbrev StandardModel := Model standardDodecad

structure CompleteConstruction (D : Dodecad) : Prop where
  finite : Finite (Model D)
  card : Nat.card (Model D) = order
  simple : IsSimpleGroup (Model D)
  noncommuting : ∃ g h : Model D, g*h ≠ h*g
  degree : Nat.card (Points D) = 12
  faithful : FaithfulSMul (Model D) (Points D)
  sharp_five : ∀ e f : Fin 5 ↪ Points D, ∃! g : Model D, g • e = f
  not_six : ¬ MulAction.IsMultiplyPretransitive (Model D) (Points D) 6
  embedding_injective : Function.Injective (embedding D)
  block_size : ∀ B ∈ Blocks D, B.card = 6
  block_count : (Blocks D).card = 132
  steiner : ∀ T : Finset (Points D), T.card = 5 → ∃! B, B ∈ Blocks D ∧ T ⊆ B
  blocks_preserved : ∀ g B, B ∈ Blocks D → mathieu12PermuteBlock D g B ∈ Blocks D
  blocks_complement : ∀ B, B ∈ Blocks D → Bᶜ ∈ Blocks D
  dodecad_orbit : ∀ E : Dodecad, ∃ g : Mathieu24CodeModel, g • D = E
  complement_stabilizer : Mathieu12DodecadModel (dodecadComplement D) = Mathieu12DodecadModel D
  complement_sharp : ∀ e f : Fin 5 ↪ Points (dodecadComplement D),
    ∃! g : Model (dodecadComplement D), g • e = f
  pair_order : Nat.card (PairModel D) = 190080
  pair_surjective : Function.Surjective (pairRestriction D)
  pair_kernel : (toPair D).range = (pairRestriction D).ker
  pair_index : (toPair D).range.index = 2
  marked_choice : ∀ (E : Dodecad) (a : Points D) (b : Points E),
    ∃ g : Mathieu24CodeModel, g • D = E ∧ g.val a.val = b.val
  m11_intersection : ∀ a : Points D, (mathieu11_to_m24 D a).range =
    Mathieu12DodecadModel D ⊓ Mathieu23PointModel a.val

theorem construction_complete (D : Dodecad) : CompleteConstruction D where
  finite := finite D
  card := card D
  simple := isSimpleGroup D
  noncommuting := exists_mul_ne_mul D
  degree := degree D
  faithful := faithful D
  sharp_five := sharp_five_transitive D
  not_six := not_six_transitive D
  embedding_injective := embedding_injective D
  block_size := mathieu12Blocks_size D
  block_count := block_count D
  steiner := steiner D
  blocks_preserved := mathieu12Blocks_preserved D
  blocks_complement := mathieu12Blocks_complement D
  dodecad_orbit := fun E => by
    obtain ⟨g,hg⟩ := dodecad_transitive_explicit D E
    exact ⟨g,Subtype.ext hg⟩
  complement_stabilizer := mathieu12_complement_stabilizer D
  complement_sharp := sharp_five_transitive (dodecadComplement D)
  pair_order := mathieu12Pair_order D
  pair_surjective := mathieu12PairRestriction_surjective D
  pair_kernel := mathieu12_to_pair_range D
  pair_index := mathieu12_pair_index D
  marked_choice := dodecad_point_flags_transitive D
  m11_intersection := mathieu11_image_intersection D

theorem exists_model (D : Dodecad) : ∃ (G : Type) (_ : Group G), Nonempty (G ≃* Model D) ∧
    Finite G ∧ Nat.card G = order ∧ IsSimpleGroup G ∧ (∃ g h : G, g*h ≠ h*g) ∧ CompleteConstruction D :=
  ⟨Model D,inferInstance,⟨MulEquiv.refl _⟩,finite D,card D,isSimpleGroup D,
    exists_mul_ne_mul D,construction_complete D⟩

end Atlas.Sporadic.Mathieu12
