import Atlas.LinearGroups.F4.ShortWeylRootSupport

namespace Atlas.F4

def shortWeylRootDestination (i : Fin 8) : Fin 24 → Fin 24 :=
  (![![7,1,2,3,4,5,6,0,20,21,22,16,23,17,18,19,11,13,14,15,8,9,10,12],
     ![0,6,2,3,4,5,1,7,18,19,16,22,17,23,20,21,10,12,8,9,14,15,11,13],
     ![0,1,5,3,4,2,6,7,17,16,19,21,18,20,23,22,9,8,12,10,13,11,15,14],
     ![0,1,2,4,3,5,6,7,16,17,18,20,19,21,22,23,8,9,10,12,11,13,14,15]] :
      Fin 4 → Fin 24 → Fin 24) (shortWeylAxis i)

def shortWeylRootSign (i : Fin 8) : Fin 24 → ℤ :=
  (![![1,-1,-1,-1,-1,-1,-1,1,1,1,-1,1,1,-1,1,1,-1,1,-1,-1,-1,-1,1,-1],
     ![-1,1,-1,-1,-1,-1,1,-1,-1,1,1,1,1,1,1,-1,-1,-1,1,-1,-1,1,-1,-1],
     ![-1,-1,1,-1,-1,1,-1,-1,1,-1,1,1,1,1,-1,1,1,-1,-1,-1,-1,-1,-1,1],
     ![-1,-1,-1,1,1,-1,-1,-1,1,1,1,-1,-1,1,1,1,-1,-1,-1,1,1,-1,-1,-1]] :
      Fin 4 → Fin 24 → ℤ) (shortWeylAxis i)

theorem shortWeylRootSign_sq : ∀ (i : Fin 8) (r : Fin 24), shortWeylRootSign i r ^ 2 = 1 := by
  decide +kernel

def shortWeylLColumn (i : Fin 8) (r : Fin 24) (j : Fin 27) : Atlas.Albert.Carrier ℤ :=
  ∑ k : Fin 12, if (shortRootLinearEntries r k).1.2 = j then
    ((shortRootLinearEntries r k).2 * shortWeylSign i (shortRootLinearEntries r k).1.1) •
      Atlas.Albert.basisVector
        (albertCoordinateOfFin (shortWeylDestination i (shortRootLinearEntries r k).1.1)) else 0

def shortWeylQColumn (i : Fin 8) (r : Fin 24) (j : Fin 27) : Atlas.Albert.Carrier ℤ :=
  if (shortRootQuadraticEntry r).1.2 = j then
    ((shortRootQuadraticEntry r).2 * shortWeylSign i (shortRootQuadraticEntry r).1.1) •
      Atlas.Albert.basisVector
        (albertCoordinateOfFin (shortWeylDestination i (shortRootQuadraticEntry r).1.1)) else 0

/-- Candidate sparse-entry reindexing, verified by the kernel below. -/
def shortWeylEntryIndex (i : Fin 8) : Fin 24 → Fin 12 → Fin 12 :=
  (![![![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,8,9,6,7,4,5,2,3,11,10],
      ![1,0,8,9,6,7,4,5,2,3,11,10],
      ![1,0,8,9,6,7,4,5,2,3,11,10],
      ![1,0,8,9,6,7,4,5,2,3,11,10],
      ![1,0,8,9,6,7,4,5,2,3,11,10],
      ![1,0,8,9,6,7,4,5,2,3,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![0,1,7,4,5,6,2,3,9,10,11,8],
      ![0,1,7,4,5,6,2,3,9,10,11,8],
      ![0,1,7,4,5,6,2,3,9,10,11,8],
      ![0,1,5,6,7,4,2,3,11,8,9,10],
      ![0,1,7,4,5,6,2,3,9,10,11,8],
      ![0,1,5,6,7,4,2,3,11,8,9,10],
      ![0,1,5,6,7,4,2,3,11,8,9,10],
      ![0,1,5,6,7,4,2,3,11,8,9,10],
      ![0,1,6,7,5,2,3,4,9,10,11,8],
      ![0,1,6,7,5,2,3,4,9,10,11,8],
      ![0,1,6,7,5,2,3,4,9,10,11,8],
      ![0,1,6,7,5,2,3,4,9,10,11,8],
      ![0,1,6,7,3,4,5,2,11,8,9,10],
      ![0,1,6,7,3,4,5,2,11,8,9,10],
      ![0,1,6,7,3,4,5,2,11,8,9,10],
      ![0,1,6,7,3,4,5,2,11,8,9,10]],
    ![![1,0,8,9,6,7,4,5,2,3,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,7,6,9,8,3,2,5,4,11,10],
      ![1,0,7,6,9,8,3,2,5,4,11,10],
      ![1,0,7,6,9,8,3,2,5,4,11,10],
      ![1,0,7,6,9,8,3,2,5,4,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,8,9,6,7,4,5,2,3,11,10],
      ![0,1,4,7,5,6,2,3,9,10,8,11],
      ![0,1,4,7,5,6,2,3,9,10,8,11],
      ![0,1,4,6,7,5,2,3,10,8,9,11],
      ![0,1,6,4,5,7,2,3,8,10,11,9],
      ![0,1,4,6,7,5,2,3,10,8,9,11],
      ![0,1,6,4,5,7,2,3,8,10,11,9],
      ![0,1,5,6,4,7,2,3,8,11,9,10],
      ![0,1,5,6,4,7,2,3,8,11,9,10],
      ![0,1,6,7,2,5,3,4,9,10,8,11],
      ![0,1,6,7,2,5,3,4,9,10,8,11],
      ![0,1,6,7,2,4,5,3,10,8,9,11],
      ![0,1,6,7,2,4,5,3,10,8,9,11],
      ![0,1,6,7,4,2,3,5,8,10,11,9],
      ![0,1,6,7,4,2,3,5,8,10,11,9],
      ![0,1,6,7,3,4,2,5,8,11,9,10],
      ![0,1,6,7,3,4,2,5,8,11,9,10]],
    ![![1,0,7,6,9,8,3,2,5,4,11,10],
      ![1,0,7,6,9,8,3,2,5,4,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,7,6,9,8,3,2,5,4,11,10],
      ![1,0,7,6,9,8,3,2,5,4,11,10],
      ![0,1,4,5,7,6,2,3,9,8,10,11],
      ![0,1,4,5,7,6,2,3,9,8,10,11],
      ![0,1,4,6,5,7,2,3,8,10,9,11],
      ![0,1,4,6,5,7,2,3,8,10,9,11],
      ![0,1,4,6,5,7,2,3,8,10,9,11],
      ![0,1,4,6,5,7,2,3,8,10,9,11],
      ![0,1,5,4,6,7,2,3,8,9,11,10],
      ![0,1,5,4,6,7,2,3,8,9,11,10],
      ![0,1,6,7,2,3,5,4,9,8,10,11],
      ![0,1,6,7,2,3,5,4,9,8,10,11],
      ![0,1,6,7,2,4,3,5,8,10,9,11],
      ![0,1,6,7,2,4,3,5,8,10,9,11],
      ![0,1,6,7,2,4,3,5,8,10,9,11],
      ![0,1,6,7,2,4,3,5,8,10,9,11],
      ![0,1,6,7,3,2,4,5,8,9,11,10],
      ![0,1,6,7,3,2,4,5,8,9,11,10]],
    ![![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![1,0,6,7,8,9,2,3,4,5,11,10],
      ![0,1,4,5,6,7,2,3,8,9,10,11],
      ![0,1,4,5,6,7,2,3,8,9,10,11],
      ![0,1,4,5,6,7,2,3,8,9,10,11],
      ![0,1,4,5,6,7,2,3,8,9,10,11],
      ![0,1,4,5,6,7,2,3,8,9,10,11],
      ![0,1,4,5,6,7,2,3,8,9,10,11],
      ![0,1,4,5,6,7,2,3,8,9,10,11],
      ![0,1,4,5,6,7,2,3,8,9,10,11],
      ![0,1,6,7,2,3,4,5,8,9,10,11],
      ![0,1,6,7,2,3,4,5,8,9,10,11],
      ![0,1,6,7,2,3,4,5,8,9,10,11],
      ![0,1,6,7,2,3,4,5,8,9,10,11],
      ![0,1,6,7,2,3,4,5,8,9,10,11],
      ![0,1,6,7,2,3,4,5,8,9,10,11],
      ![0,1,6,7,2,3,4,5,8,9,10,11],
      ![0,1,6,7,2,3,4,5,8,9,10,11]]] : Fin 4 → Fin 24 → Fin 12 → Fin 12) (shortWeylAxis i)

/-- The reflected-root entry reindexing is inverse to the original one. -/
theorem shortWeylEntryIndex_inverse : ∀ (i : Fin 8) (r : Fin 24) (k : Fin 12),
    shortWeylEntryIndex i (shortWeylRootDestination i r) (shortWeylEntryIndex i r k) = k ∧
    shortWeylEntryIndex i r (shortWeylEntryIndex i (shortWeylRootDestination i r) k) = k := by
  decide +kernel

def shortWeylEntryPermutation (i : Fin 8) (r : Fin 24) : Equiv.Perm (Fin 12) where
  toFun := shortWeylEntryIndex i r
  invFun := shortWeylEntryIndex i (shortWeylRootDestination i r)
  left_inv k := (shortWeylEntryIndex_inverse i r k).1
  right_inv k := (shortWeylEntryIndex_inverse i r k).2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Sparse signed-matrix identities: only twelve entries per root, not 27² coordinates. -/
theorem shortWeyl_entry_identity : ∀ (i : Fin 8) (r : Fin 24) (k : Fin 12),
    (shortRootLinearEntries (shortWeylRootDestination i r) (shortWeylEntryIndex i r k)).1.1 =
      shortWeylDestination i (shortRootLinearEntries r k).1.1 ∧
    (shortRootLinearEntries (shortWeylRootDestination i r) (shortWeylEntryIndex i r k)).1.2 =
      shortWeylDestination i (shortRootLinearEntries r k).1.2 ∧
    (shortRootLinearEntries r k).2 * shortWeylSign i (shortRootLinearEntries r k).1.1 =
      (shortWeylRootSign i r * shortWeylSign i (shortRootLinearEntries r k).1.2) *
        (shortRootLinearEntries (shortWeylRootDestination i r) (shortWeylEntryIndex i r k)).2 := by
  decide +kernel

theorem shortWeyl_quadratic_entry_identity : ∀ (i : Fin 8) (r : Fin 24),
    (shortRootQuadraticEntry (shortWeylRootDestination i r)).1.1 =
      shortWeylDestination i (shortRootQuadraticEntry r).1.1 ∧
    (shortRootQuadraticEntry (shortWeylRootDestination i r)).1.2 =
      shortWeylDestination i (shortRootQuadraticEntry r).1.2 ∧
    (shortRootQuadraticEntry r).2 * shortWeylSign i (shortRootQuadraticEntry r).1.1 =
      shortWeylSign i (shortRootQuadraticEntry r).1.2 *
        (shortRootQuadraticEntry (shortWeylRootDestination i r)).2 := by
  decide +kernel

theorem shortWeyl_L_column_identity (i : Fin 8) (r : Fin 24) (j : Fin 27) :
    shortWeylLColumn i r j = (shortWeylRootSign i r * shortWeylSign i j) •
      shortRootLinearColumn (shortWeylRootDestination i r) (shortWeylDestination i j) := by
  classical
  unfold shortWeylLColumn shortRootLinearColumn
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (shortWeylEntryPermutation i r)
  intro k
  rw [show (shortWeylEntryPermutation i r) k = shortWeylEntryIndex i r k from rfl]
  obtain ⟨ha,hb,hc⟩ := shortWeyl_entry_identity i r k
  rw [ha,hb]
  by_cases h : (shortRootLinearEntries r k).1.2 = j
  · simp only [h, if_pos, smul_smul]
    rw [h] at hc
    rw [hc]
  · have hh : shortWeylDestination i (shortRootLinearEntries r k).1.2 ≠
        shortWeylDestination i j := fun hh => h ((shortWeylPermutation i).injective hh)
    simp only [h, hh, if_false, smul_zero]

theorem shortWeyl_Q_column_identity (i : Fin 8) (r : Fin 24) (j : Fin 27) :
    shortWeylQColumn i r j = shortWeylSign i j •
      shortRootQuadraticColumn (shortWeylRootDestination i r) (shortWeylDestination i j) := by
  unfold shortWeylQColumn shortRootQuadraticColumn
  obtain ⟨ha,hb,hc⟩ := shortWeyl_quadratic_entry_identity i r
  rw [ha,hb]
  by_cases h : (shortRootQuadraticEntry r).1.2 = j
  · simp only [h, if_pos, smul_smul]
    rw [h] at hc
    rw [hc]
  · have hh : shortWeylDestination i (shortRootQuadraticEntry r).1.2 ≠
        shortWeylDestination i j := fun hh => h ((shortWeylPermutation i).injective hh)
    simp only [h, hh, if_false, smul_zero]

end Atlas.F4
