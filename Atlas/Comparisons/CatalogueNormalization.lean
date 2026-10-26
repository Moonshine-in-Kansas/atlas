import Atlas.Comparisons.CatalogueModels
import Atlas.Comparisons.SameFieldSize
import Atlas.OrderArithmetic.Normalization
import Atlas.Comparisons.Exceptional.Order60Four
import Atlas.Comparisons.Exceptional.Order60Five
import Atlas.Comparisons.Exceptional.Order168
import Atlas.Comparisons.Exceptional.Order360
import Atlas.Comparisons.Exceptional.Order20160A8
import Atlas.Comparisons.Exceptional.Order25920

/-! Every arithmetic normalization is realized by a proved isomorphism between
actual ATLAS groups. No equality of cardinalities is used for recognition. -/
noncomputable section
namespace Atlas.Comparisons.Catalogue
open Atlas.OrderArithmetic

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private def primeField (p : ℕ) [Fact p.Prime] : FiniteField where
  carrier := ZMod p

private theorem cThree_admissible : Admissible (.C 2 (Nat.card (ZMod 3))) := by
  norm_num [Admissible, Nat.card_zmod]
  exact ⟨3, 1, by norm_num, by norm_num, by norm_num⟩

private theorem linearSeven_admissible : Admissible (.linear 2 (Nat.card (ZMod 7))) := by
  norm_num [Admissible, Nat.card_zmod]
  exact ⟨7, 1, by norm_num, by norm_num, by norm_num⟩

/-- Existence of an actual normalized construction and an actual isomorphism. -/
theorem exists_normalized (x : Entry) :
    ∃ y : Entry, label y = OrderArithmetic.normalize (label x) ∧ Nonempty (Model x ≃* Model y) := by
  classical
  cases x with
  | linear F d h =>
    by_cases h60 : d = 2 ∧ (Nat.card F.carrier = 4 ∨ Nat.card F.carrier = 5)
    · rcases h60 with ⟨rfl, hq | hq⟩
      · refine ⟨.alternating 5 (by decide), ?_, ?_⟩
        · simp [label, OrderArithmetic.normalize, hq]
        · exact ⟨Exceptional.psl2Card4EquivAlt5 hq⟩
      · refine ⟨.alternating 5 (by decide), ?_, ?_⟩
        · simp [label, OrderArithmetic.normalize, hq]
        · exact ⟨Exceptional.psl2Card5EquivAlt5 hq⟩
    by_cases h360 : d = 2 ∧ Nat.card F.carrier = 9
    · rcases h360 with ⟨rfl, hq⟩
      refine ⟨.alternating 6 (by decide), ?_, ?_⟩
      · simp [label, OrderArithmetic.normalize, hq]
      · exact ⟨Exceptional.psl2Card9EquivAlt6 hq⟩
    by_cases h168 : d = 3 ∧ Nat.card F.carrier = 2
    · rcases h168 with ⟨rfl, hq⟩
      refine ⟨.linear (primeField 7) 2 linearSeven_admissible, ?_, ?_⟩
      · simp [label, OrderArithmetic.normalize, hq, primeField, Nat.card_zmod]
      · exact ⟨(Atlas.fieldEquivPSL 3 (SameFieldSize.fieldEquiv
          (show Nat.card F.carrier = Nat.card (ZMod 2) by simpa using hq))).trans
            Exceptional.psl2SevenEquivPsl3Two.symm⟩
    by_cases h20160 : d = 4 ∧ Nat.card F.carrier = 2
    · rcases h20160 with ⟨rfl, hq⟩
      refine ⟨.alternating 8 (by decide), ?_, ?_⟩
      · simp [label, OrderArithmetic.normalize, hq]
      · exact ⟨(Atlas.fieldEquivPSL 4 (SameFieldSize.fieldEquiv
          (show Nat.card F.carrier = Nat.card (ZMod 2) by simpa using hq))).trans
            Exceptional.psl4TwoEquivAlt8⟩
    refine ⟨.linear F d h, ?_, ⟨MulEquiv.refl _⟩⟩
    simp [label, OrderArithmetic.normalize, h60, h360, h168, h20160]
  | unitary E d h =>
    by_cases h25920 : d = 4 ∧ Nat.card E.base.carrier = 2
    · rcases h25920 with ⟨rfl, hq⟩
      refine ⟨.C (primeField 3) 2 cThree_admissible, ?_, ?_⟩
      · simp [label, OrderArithmetic.normalize, hq, primeField, Nat.card_zmod]
      · exact ⟨Exceptional.psu4Card2EquivPSp4Card3 E.finrank hq
          (show Nat.card (ZMod 3) = 3 by simp)⟩
    refine ⟨.unitary E d h, ?_, ⟨MulEquiv.refl _⟩⟩
    simp [label, OrderArithmetic.normalize, h25920]
  | B F r h =>
    by_cases hn : r = 2 ∨ (3 ≤ r ∧ Even (Nat.card F.carrier))
    · refine ⟨.C F r h, ?_, ?_⟩
      · simp [label, OrderArithmetic.normalize, hn]
      · rcases hn with rfl | ⟨hr, hq⟩
        · exact ⟨Classical.b2EquivC2⟩
        · have h2 : (2 : F.carrier) = 0 := by
            by_contra hh
            have ho := Atlas.odd_card_mod_two hh
            have he := Nat.even_iff.mp hq
            omega
          letI : CharP F.carrier 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
          exact ⟨Classical.evenBEquivC r (by omega)⟩
    refine ⟨.B F r h, ?_, ⟨MulEquiv.refl _⟩⟩
    simp [label, OrderArithmetic.normalize, hn]
  | cyclic p h => exact ⟨.cyclic p h, rfl, ⟨MulEquiv.refl _⟩⟩
  | alternating n h => exact ⟨.alternating n h, rfl, ⟨MulEquiv.refl _⟩⟩
  | C F r h => exact ⟨.C F r h, rfl, ⟨MulEquiv.refl _⟩⟩
  | Dplus F r h => exact ⟨.Dplus F r h, rfl, ⟨MulEquiv.refl _⟩⟩
  | Dminus E r h => exact ⟨.Dminus E r h, rfl, ⟨MulEquiv.refl _⟩⟩
  | G2 F h => exact ⟨.G2 F h, rfl, ⟨MulEquiv.refl _⟩⟩
  | F4 F h => exact ⟨.F4 F h, rfl, ⟨MulEquiv.refl _⟩⟩
  | triality E h => exact ⟨.triality E h, rfl, ⟨MulEquiv.refl _⟩⟩
  | suzuki F m hm hc => exact ⟨.suzuki F m hm hc, rfl, ⟨MulEquiv.refl _⟩⟩
  | smallRee F m hm hc => exact ⟨.smallRee F m hm hc, rfl, ⟨MulEquiv.refl _⟩⟩
  | fixed z => exact ⟨.fixed z, rfl, ⟨MulEquiv.refl _⟩⟩

/-- A normalized entry chosen together with its previously proved comparison. -/
def normalizedEntry (x : Entry) : Entry := (exists_normalized x).choose

theorem normalizedEntry_label (x : Entry) :
    label (normalizedEntry x) = OrderArithmetic.normalize (label x) :=
  (exists_normalized x).choose_spec.1

def normalizeEquiv (x : Entry) : Model x ≃* Model (normalizedEntry x) :=
  (exists_normalized x).choose_spec.2.some

end Atlas.Comparisons.Catalogue
