import Atlas.OrderArithmetic.FiniteTables
import Atlas.OrderArithmetic.SecondIndexBounds

namespace Atlas.OrderArithmetic

/-- Necessary and sufficient range test within the displayed binary classical box. -/
def binaryRange : RawEntry → Bool
  | .linear d q => decide (2 ≤ d ∧ ¬ (d = 2 ∧ (q = 2 ∨ q = 3)))
  | .unitary d q => decide (3 ≤ d ∧ ¬ (d = 3 ∧ q = 2))
  | .B r q | .C r q => decide (2 ≤ r ∧ ¬ (r = 2 ∧ q = 2))
  | .Dplus r _ | .Dminus r _ => decide (4 ≤ r)
  | _ => false

def binaryClassicalAt (f : ℕ) : Finset RawEntry :=
  (Finset.Icc 2 7).biUnion fun r => (classicalAt r (2 ^ f)).filter (binaryRange ·)

def binaryClassicalBox : Finset RawEntry :=
  (Finset.Icc 1 6).biUnion binaryClassicalAt

theorem binaryRange_of_admissible {x : RawEntry} (hx : Admissible x)
    (hc : IsClassicalLie x) : binaryRange x = true := by
  cases x <;> simp_all [IsClassicalLie, binaryRange, Admissible]

theorem mem_binaryClassicalBox {x : RawEntry} {f : ℕ}
    (hx : Admissible x) (hc : IsClassicalLie x) (hf : 1 ≤ f) (hf6 : f ≤ 6)
    (hq : fieldSize x = 2 ^ f) (hr : rankParameter x ≤ 7) : x ∈ binaryClassicalBox := by
  apply Finset.mem_biUnion.mpr
  refine ⟨f, Finset.mem_Icc.mpr ⟨hf, hf6⟩, ?_⟩
  have hb := binaryRange_of_admissible hx hc
  cases x with
  | linear r q | unitary r q | B r q | C r q | Dplus r q | Dminus r q =>
    change q = 2 ^ f at hq
    subst q
    apply Finset.mem_biUnion.mpr
    refine ⟨r, Finset.mem_Icc.mpr ⟨?_, hr⟩, Finset.mem_filter.mpr ⟨?_, hb⟩⟩
    · have := hx.1; omega
    · simp [classicalAt]
  | _ => contradiction

/-- A computable syntactic relation for the finite binary table only. -/
def BinaryCollision (x y : RawEntry) : Prop :=
  normalize x = normalize y ∨
    (x = .linear 4 2 ∧ y = .linear 3 4) ∨ (y = .linear 4 2 ∧ x = .linear 3 4)

instance (x y : RawEntry) : Decidable (BinaryCollision x y) := inferInstanceAs
  (Decidable (normalize x = normalize y ∨
    (x = .linear 4 2 ∧ y = .linear 3 4) ∨ (y = .linear 4 2 ∧ x = .linear 3 4)))

theorem binaryCollision_collision {x y : RawEntry} (h : BinaryCollision x y) : Collision x y := by
  rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl h
  all_goals norm_num [Collision, normalize, Exceptional]

end Atlas.OrderArithmetic
