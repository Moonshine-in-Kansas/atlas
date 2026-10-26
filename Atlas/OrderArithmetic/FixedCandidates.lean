import Atlas.OrderArithmetic.Positivity
import Mathlib.Data.Finset.Union

namespace Atlas.OrderArithmetic

def rankParameter : RawEntry → ℕ
  | .linear d _ | .unitary d _ => d
  | .B r _ | .C r _ | .Dplus r _ | .Dminus r _ => r
  | _ => 0

theorem rank_le_characteristicExponent_add_one {x : RawEntry} (hx : Admissible x) :
    rankParameter x ≤ characteristicExponent x + 1 := by
  cases x with
  | linear d q | unitary d q =>
    have hd : 2 ≤ d := by have := hx.1; omega
    have hm : 2 * (d - 1) ≤ d * (d - 1) := Nat.mul_le_mul_right _ hd
    change d ≤ d * (d - 1) / 2 + 1
    omega
  | B r q | C r q =>
    change r ≤ r ^ 2 + 1
    nlinarith [sq_nonneg (r - 1 : ℤ)]
  | Dplus r q | Dminus r q =>
    have hr : 4 ≤ r := hx.1
    have hs : 1 ≤ r - 1 := by omega
    have := Nat.mul_le_mul_left r hs
    change r ≤ r * (r - 1) + 1
    omega
  | _ => simp [rankParameter]

def classicalAt (r q : ℕ) : Finset RawEntry :=
  {.linear r q, .unitary r q, .B r q, .C r q, .Dplus r q, .Dminus r q}

def exceptionalAt (q : ℕ) : Finset RawEntry :=
  {.G2 q, .F4 q, .E6 q, .E7 q, .E8 q, .twistedE6 q, .trialityD4 q,
    .suzuki q, .smallRee q, .largeRee q}

/-- A small finite over-approximation, filtered by exponent and admissibility later. -/
def ordinaryAt (q a : ℕ) : Finset RawEntry :=
  ((Finset.Icc 2 (a + 1)).biUnion fun r => classicalAt r q) ∪ exceptionalAt q

theorem self_mem_ordinaryAt {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    x ∈ ordinaryAt (fieldSize x) (characteristicExponent x) := by
  have hr := rank_le_characteristicExponent_add_one hx
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear r q | unitary r q | B r q | C r q | Dplus r q | Dminus r q =>
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_Icc.mpr ⟨?_, hr⟩, ?_⟩
    · have := hx.1; omega
    · simp [classicalAt, fieldSize]
  | _ => simp [ordinaryAt, exceptionalAt, fieldSize]

/-- Enumeration uses prime support and characteristic valuations, never q ≤ M. -/
def lieCandidates (M : ℕ) : Finset RawEntry :=
  M.primeFactors.biUnion fun p =>
    ((Finset.Icc 1 (M.factorization p)).filter fun f => f ∣ M.factorization p).biUnion
      fun f => ordinaryAt (p ^ f) (M.factorization p / f)

/-- Unconditional completeness of the finite generator for every fixed integer. -/
theorem mem_lieCandidates_of_order_eq {x : RawEntry} {M : ℕ}
    (hx : Admissible x) (hl : IsLie x) (hM : order x = M) : x ∈ lieCandidates M := by
  obtain ⟨p, f, hp, hf, hq⟩ := lie_field_primePower hx hl
  have ha := characteristicExponent_pos hx hl
  have hv : M.factorization p = f * characteristicExponent x := by
    rw [← hM]
    exact order_characteristic_valuation hx hl hp hf hq
  have hpos : M ≠ 0 := by have := lie_order_pos hx hl; omega
  have hpM : p ∣ M := (hp.dvd_iff_one_le_factorization hpos).mpr (by rw [hv]; nlinarith)
  apply Finset.mem_biUnion.mpr
  refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpM, hpos⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hf, ?_⟩, ?_⟩, ?_⟩
  · rw [hv]; nlinarith
  · exact ⟨characteristicExponent x, hv⟩
  · rw [hv, Nat.mul_div_cancel_left _ (by omega : 0 < f), ← hq]
    exact self_mem_ordinaryAt hx hl

end Atlas.OrderArithmetic
