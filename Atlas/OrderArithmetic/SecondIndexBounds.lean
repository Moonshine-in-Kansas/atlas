import Atlas.OrderArithmetic.IndexBounds

namespace Atlas.OrderArithmetic

/-! Finite coverage consequences of the numerical index profiles. These statements
do not identify cyclotomic supports or derive an index bound from equal orders. -/

def IsClassicalLie : RawEntry → Prop
  | .linear _ _ | .unitary _ _ | .B _ _ | .C _ _ | .Dplus _ _ | .Dminus _ _ => True
  | _ => False

/-- The numerical second-index table, with the two small unitary dimensions
specified separately. Its cyclotomic interpretation is a separate obligation. -/
def secondIndex : RawEntry → ℕ
  | .linear d _ => d - 1
  | .unitary d _ =>
    if d = 3 then 2 else if d = 4 then 4 else
      if Even d then 2 * (d - 3) else 2 * (d - 2)
  | .B r _ | .C r _ | .Dminus r _ => 2 * (r - 1)
  | .Dplus r _ => 2 * (r - 2)
  | _ => 0

theorem classical_isLie {x : RawEntry} (hx : IsClassicalLie x) : IsLie x := by
  cases x <;> simp_all [IsClassicalLie, IsLie]

theorem classical_rank_two_le {x : RawEntry} (hx : Admissible x)
    (hc : IsClassicalLie x) : 2 ≤ rankParameter x := by
  cases x with
  | linear d q | unitary d q | B d q | C d q | Dplus d q | Dminus d q =>
    have hd := hx.1
    simp only [rankParameter]
    omega
  | _ => simp_all [IsClassicalLie]

theorem secondIndex_one_le {x : RawEntry} (hx : Admissible x)
    (hc : IsClassicalLie x) : 1 ≤ secondIndex x := by
  cases x with
  | linear d q =>
    have hd := hx.1
    simp only [secondIndex]
    omega
  | unitary d q =>
    have hd := hx.1
    simp only [secondIndex]
    split_ifs <;> omega
  | B r q | C r q | Dplus r q | Dminus r q =>
    have hr := hx.1
    simp only [secondIndex]
    omega
  | _ => simp_all [IsClassicalLie]

theorem secondIndex_lt_topIndex {x : RawEntry} (hx : Admissible x)
    (hc : IsClassicalLie x) : secondIndex x < topIndex x := by
  cases x with
  | linear d q =>
    have hd := hx.1
    simp only [secondIndex, topIndex]
    omega
  | unitary d q =>
    have hd := hx.1
    simp only [secondIndex, topIndex]
    split_ifs <;> omega
  | B r q | C r q | Dplus r q | Dminus r q =>
    have hr := hx.1
    simp only [secondIndex, topIndex]
    omega
  | _ => simp_all [IsClassicalLie]

theorem classical_rank_le_secondIndex_add_one {x : RawEntry}
    (hx : Admissible x) (hc : IsClassicalLie x) :
    rankParameter x ≤ secondIndex x + 1 := by
  cases x with
  | linear d q =>
    have hd := hx.1
    simp only [secondIndex, rankParameter]
    omega
  | unitary d q =>
    have hd := hx.1
    simp only [secondIndex, rankParameter]
    split_ifs <;> omega
  | B r q | C r q | Dplus r q | Dminus r q =>
    have hr := hx.1
    simp only [secondIndex, rankParameter]
    omega
  | _ => simp_all [IsClassicalLie]

theorem bounds_of_scaled_topIndex_le_six {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x) (hf : 1 ≤ f)
    (h : f * topIndex x ≤ 6) : f ≤ 6 ∧ rankParameter x ≤ 7 := by
  have hm := topIndex_two_le hx (classical_isLie hc)
  have hs := secondIndex_lt_topIndex hx hc
  have hr := classical_rank_le_secondIndex_add_one hx hc
  have hfm := Nat.mul_le_mul_left f (show 1 ≤ topIndex x by omega)
  have hmf := Nat.mul_le_mul_right (topIndex x) hf
  constructor <;> nlinarith

theorem bounds_of_scaled_secondIndex_le_six {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x) (hf : 1 ≤ f)
    (h : f * secondIndex x ≤ 6) : f ≤ 6 ∧ rankParameter x ≤ 7 := by
  have hs := secondIndex_one_le hx hc
  have hr := classical_rank_le_secondIndex_add_one hx hc
  have hfs := Nat.mul_le_mul_left f hs
  have hsf := Nat.mul_le_mul_right (secondIndex x) hf
  constructor <;> nlinarith

/-- The over-approximation specified for the two binary primitive-index branches.
Admissibility remains a separate filter; no completeness claim about order
collisions is built into this definition. -/
def binaryIndexCandidates : Finset RawEntry :=
  (Finset.Icc 1 6).biUnion fun f =>
    (Finset.Icc 2 7).biUnion fun r => classicalAt r (2 ^ f)

theorem classical_mem_classicalAt {x : RawEntry} (hc : IsClassicalLie x) :
    x ∈ classicalAt (rankParameter x) (fieldSize x) := by
  cases x <;> simp_all [IsClassicalLie, classicalAt, rankParameter, fieldSize]

theorem mem_binaryIndexCandidates_of_bounds {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x) (hf : 1 ≤ f) (hf6 : f ≤ 6)
    (hr7 : rankParameter x ≤ 7) (hq : fieldSize x = 2 ^ f) :
    x ∈ binaryIndexCandidates := by
  apply Finset.mem_biUnion.mpr
  refine ⟨f, Finset.mem_Icc.mpr ⟨hf, hf6⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨rankParameter x, Finset.mem_Icc.mpr ⟨classical_rank_two_le hx hc, hr7⟩, ?_⟩
  simpa only [hq] using classical_mem_classicalAt hc

theorem mem_binaryIndexCandidates_of_topIndex_bound {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x) (hf : 1 ≤ f)
    (hq : fieldSize x = 2 ^ f) (h : f * topIndex x ≤ 6) :
    x ∈ binaryIndexCandidates := by
  obtain ⟨hf6, hr7⟩ := bounds_of_scaled_topIndex_le_six hx hc hf h
  exact mem_binaryIndexCandidates_of_bounds hx hc hf hf6 hr7 hq

theorem mem_binaryIndexCandidates_of_secondIndex_bound {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x) (hf : 1 ≤ f)
    (hq : fieldSize x = 2 ^ f) (h : f * secondIndex x ≤ 6) :
    x ∈ binaryIndexCandidates := by
  obtain ⟨hf6, hr7⟩ := bounds_of_scaled_secondIndex_le_six hx hc hf h
  exact mem_binaryIndexCandidates_of_bounds hx hc hf hf6 hr7 hq

end Atlas.OrderArithmetic
