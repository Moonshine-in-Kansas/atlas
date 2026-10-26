import Atlas.OrderArithmetic.Classification

namespace Atlas.OrderArithmetic

/-- Explicit coverage list for the fixed-label transcription in the specification. -/
def specificationFixedLabels : List FixedLabel :=
  [.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .McL, .He, .Ru,
    .Suz, .ON, .Co3, .Co2, .Fi22, .HN, .Ly, .Th, .Fi23, .Co1, .Fi24prime,
    .Baby, .Monster, .Tits]

theorem specification_fixed_count : specificationFixedLabels.length = 27 := by decide

theorem specification_fixed_complete (s : FixedLabel) : s ∈ specificationFixedLabels := by
  cases s <;> decide

theorem specification_fixed_distinct : specificationFixedLabels.Nodup := by decide

theorem specification_fixed_admissible (s : FixedLabel) : Admissible (.fixed s) := by trivial

/-- One admissible sample of every ordinary-family constructor. -/
def specificationLieExamples : List RawEntry :=
  [.linear 2 4, .unitary 3 4, .B 2 4, .C 2 4, .Dplus 4 4, .Dminus 4 4,
    .G2 4, .F4 4, .E6 4, .E7 4, .E8 4, .twistedE6 4, .trialityD4 4,
    .suzuki 8, .smallRee 27, .largeRee 8]

/-- Pattern matching makes constructor coverage an explicit compilation check. -/
def specificationFamilyRepresentative : RawEntry → RawEntry
  | .linear _ _ => .linear 2 4
  | .unitary _ _ => .unitary 3 4
  | .B _ _ => .B 2 4
  | .C _ _ => .C 2 4
  | .Dplus _ _ => .Dplus 4 4
  | .Dminus _ _ => .Dminus 4 4
  | .G2 _ => .G2 4
  | .F4 _ => .F4 4
  | .E6 _ => .E6 4
  | .E7 _ => .E7 4
  | .E8 _ => .E8 4
  | .twistedE6 _ => .twistedE6 4
  | .trialityD4 _ => .trialityD4 4
  | .suzuki _ => .suzuki 8
  | .smallRee _ => .smallRee 27
  | .largeRee _ => .largeRee 8
  | .cyclic _ | .alternating _ | .fixed _ => .linear 2 4

theorem specification_lie_examples_admissible :
    ∀ x ∈ specificationLieExamples, Admissible x ∧ IsLie x := by
  have h4 : PrimePower 4 := ⟨2, 2, by decide, by decide, by decide⟩
  have h8 : ∃ m : ℕ, 1 ≤ m ∧ 8 = 2 ^ (2 * m + 1) := ⟨1, by decide, by decide⟩
  have h27 : ∃ m : ℕ, 1 ≤ m ∧ 27 = 3 ^ (2 * m + 1) := ⟨1, by decide, by decide⟩
  simp [specificationLieExamples, Admissible, IsLie, h4, h8, h27]

theorem specification_every_lie_constructor (x : RawEntry) (hx : IsLie x) :
    specificationFamilyRepresentative x ∈ specificationLieExamples ∧
      Admissible (specificationFamilyRepresentative x) := by
  have hm : specificationFamilyRepresentative x ∈ specificationLieExamples := by
    cases x <;> simp [specificationFamilyRepresentative, specificationLieExamples]
  exact ⟨hm, (specification_lie_examples_admissible _ hm).1⟩

/-- A field characteristic and exponent well beyond the finite diagnostic
examples, checked by the same public admissibility definition. -/
theorem specification_large_prime_power : PrimePower (101 ^ 31) :=
  ⟨101, 31, by norm_num, by decide, rfl⟩

theorem specification_large_BC_exception :
    Admissible (.B 5 (101 ^ 31)) ∧ Admissible (.C 5 (101 ^ 31)) ∧
      normalize (.B 5 (101 ^ 31)) ≠ normalize (.C 5 (101 ^ 31)) ∧
      Collision (.B 5 (101 ^ 31)) (.C 5 (101 ^ 31)) := by
  have hx : Admissible (.B 5 (101 ^ 31)) := by
    exact ⟨by decide, specification_large_prime_power, by simp⟩
  have hy : Admissible (.C 5 (101 ^ 31)) := hx
  have ho : Odd (101 ^ 31 : ℕ) := (by decide : Odd (101 : ℕ)).pow
  have hn : ¬ Even (101 ^ 31 : ℕ) := Nat.not_even_iff_odd.mpr ho
  refine ⟨hx, hy, ?_, ?_⟩
  · simp only [normalize, hn, and_false, or_false, show (5 : ℕ) ≠ 2 by decide, if_false]
    intro hh
    cases hh
  · exact (catalogue_order_eq_iff hx hy).mp (order_B_eq_C _ _)

/-- An explicit large-parameter noncollision uses the unrestricted public
theorem, without evaluating either enormous integer order. -/
theorem specification_large_noncollision :
    order (.linear 7 (101 ^ 31)) ≠ order (.unitary 9 (101 ^ 31)) := by
  have hx : Admissible (.linear 7 (101 ^ 31)) :=
    ⟨by decide, specification_large_prime_power, by simp⟩
  have hy : Admissible (.unitary 9 (101 ^ 31)) :=
    ⟨by decide, specification_large_prime_power, by simp⟩
  apply catalogue_order_ne hx hy
  simp [Collision, normalize, Exceptional]

end Atlas.OrderArithmetic
