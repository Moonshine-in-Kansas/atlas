import Atlas.OrderArithmetic.PolynomialDenominators
import Mathlib.Data.Finset.Prod

namespace Atlas.OrderArithmetic

/-! Finite family/rank coverage for the exceptional polynomial comparison rows.
Field parameters are erased, not bounded. The ratio equality remains an explicit
hypothesis, and no polynomial-row evaluation is asserted in this module. -/

/-- Ordinary-family rank bounds, without any field or simplicity restrictions. -/
def LieRankValid : RawEntry → Prop
  | .linear d _ => 2 ≤ d
  | .unitary d _ => 3 ≤ d
  | .B r _ | .C r _ => 2 ≤ r
  | .Dplus r _ | .Dminus r _ => 4 ≤ r
  | x => IsExceptionalLie x

instance : DecidablePred IsExceptionalLie := fun x => by
  cases x <;> dsimp only [IsExceptionalLie] <;> infer_instance

instance : DecidablePred LieRankValid := fun x => by
  cases x <;> dsimp only [LieRankValid] <;> infer_instance

@[simp] theorem lieRankValid_withField (x : RawEntry) (q : ℕ) :
    LieRankValid (withField x q) ↔ LieRankValid x := by
  cases x <;> rfl

theorem lieRankValid_of_admissible {x : RawEntry} (hx : Admissible x) (hl : IsLie x) :
    LieRankValid x := by
  cases x with
  | linear d q | unitary d q | B d q | C d q | Dplus d q | Dminus d q => exact hx.1
  | cyclic _ | alternating _ | fixed _ => contradiction
  | _ => trivial

theorem exceptionalPartnerRankBound_le_seventeen (x : RawEntry) :
    exceptionalPartnerRankBound x ≤ 17 := by
  cases x <;> norm_num [exceptionalPartnerRankBound]

/-- The ten exceptional templates and bounded classical templates, all at field
coordinate zero. Filtering gives L dimensions 2..9, U dimensions 3..17, B/C
ranks 2..8, D+ ranks 4..8 and D- ranks 4..9. -/
def exceptionalRankTemplates : Finset RawEntry :=
  (ordinaryAt 0 17).filter fun x =>
    LieRankValid x ∧ rankParameter x ≤ exceptionalPartnerRankBound x

theorem withField_mem_ordinaryAt_seventeen {x : RawEntry}
    (hx : Admissible x) (hl : IsLie x) (hr : rankParameter x ≤ 17) :
    withField x 0 ∈ ordinaryAt 0 17 := by
  cases x with
  | cyclic _ | alternating _ | fixed _ => contradiction
  | linear r q | unitary r q | B r q | C r q | Dplus r q | Dminus r q =>
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · have := hx.1
      omega
    · change r ≤ 17 at hr
      omega
    · simp [classicalAt, withField]
  | _ => simp [ordinaryAt, exceptionalAt, withField]

theorem withField_mem_exceptionalRankTemplates {x : RawEntry}
    (hx : Admissible x) (hl : IsLie x)
    (hr : rankParameter x ≤ exceptionalPartnerRankBound x) :
    withField x 0 ∈ exceptionalRankTemplates := by
  apply Finset.mem_filter.mpr
  refine ⟨withField_mem_ordinaryAt_seventeen hx hl
    (hr.trans (exceptionalPartnerRankBound_le_seventeen x)), ?_⟩
  constructor
  · simpa only [lieRankValid_withField] using lieRankValid_of_admissible hx hl
  · cases x <;> simpa only [withField, rankParameter, exceptionalPartnerRankBound] using hr

/-- Ordered, distinct, positive-exponent rows with at least one exceptional
family and equal characteristic/top-index ratios. -/
def ExceptionalPairCondition (z : RawEntry × RawEntry) : Prop :=
  (IsExceptionalLie z.1 ∨ IsExceptionalLie z.2) ∧
  0 < characteristicExponent z.1 ∧ 0 < characteristicExponent z.2 ∧
  LieRankValid z.1 ∧ LieRankValid z.2 ∧
  characteristicExponent z.1 * topIndex z.2 =
    characteristicExponent z.2 * topIndex z.1 ∧ z.1 ≠ z.2

instance : DecidablePred ExceptionalPairCondition := fun z => by
  unfold ExceptionalPairCondition
  infer_instance

def exceptionalPairCandidates : Finset (RawEntry × RawEntry) :=
  (exceptionalRankTemplates.product exceptionalRankTemplates).filter ExceptionalPairCondition

theorem exceptional_pair_rank_bounds {x y : RawEntry}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hex : IsExceptionalLie x ∨ IsExceptionalLie y)
    (hratio : characteristicExponent x * topIndex y =
      characteristicExponent y * topIndex x) :
    rankParameter x ≤ exceptionalPartnerRankBound x ∧
      rankParameter y ≤ exceptionalPartnerRankBound y := by
  rcases hex with hex | hey
  · exact ⟨rank_le_exceptionalPartnerRankBound hx
      (exceptional_exponent_le_four_topIndex hex),
      rank_bound_of_exceptional_ratio hy hx hlx hex hratio.symm⟩
  · exact ⟨rank_bound_of_exceptional_ratio hx hy hly hey hratio,
      rank_le_exceptionalPartnerRankBound hy (exceptional_exponent_le_four_topIndex hey)⟩

set_option maxRecDepth 4096 in
/-- Every admissible ordinary-family pair in the exceptional-ratio branch is
covered by the explicit finite row set; its field sizes remain arbitrary. -/
theorem mem_exceptionalPairCandidates_of_ratio {x y : RawEntry}
    (hx : Admissible x) (hy : Admissible y) (hlx : IsLie x) (hly : IsLie y)
    (hex : IsExceptionalLie x ∨ IsExceptionalLie y)
    (hratio : characteristicExponent x * topIndex y =
      characteristicExponent y * topIndex x)
    (hne : withField x 0 ≠ withField y 0) :
    (withField x 0, withField y 0) ∈ exceptionalPairCandidates := by
  change (withField x 0, withField y 0) ∈
    (exceptionalRankTemplates.product exceptionalRankTemplates).filter ExceptionalPairCondition
  obtain ⟨hrx, hry⟩ := exceptional_pair_rank_bounds hx hy hlx hly hex hratio
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨withField_mem_exceptionalRankTemplates hx hlx hrx,
    withField_mem_exceptionalRankTemplates hy hly hry⟩, ?_⟩
  simp only [ExceptionalPairCondition, isExceptionalLie_withField,
    characteristicExponent_withField, topIndex_withField, lieRankValid_withField]
  exact ⟨hex, by have := characteristicExponent_pos hx hlx; omega,
    by have := characteristicExponent_pos hy hly; omega,
    lieRankValid_of_admissible hx hlx, lieRankValid_of_admissible hy hly, hratio, hne⟩

end Atlas.OrderArithmetic
