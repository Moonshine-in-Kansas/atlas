import Atlas.Conway.OrthogonalFourGeometry

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem oddMinimumVector_at_mark (a : Omega) (c : golay) :
    (oddMinimumVector a c).val a = 3 ∨ (oddMinimumVector a c).val a = -3 := by
  by_cases hc : c.val a = 0 <;> simp [oddMinimumVector,signedOddProfile,signChange,oddProfileBase,hc]

theorem oddMinimumVector_off_mark (a k : Omega) (c : golay) (hk : k ≠ a) :
    (oddMinimumVector a c).val k = 1 ∨ (oddMinimumVector a c).val k = -1 := by
  by_cases hc : c.val k = 0 <;> simp [oddMinimumVector,signedOddProfile,signChange,oddProfileBase,hc,hk]

theorem orthogonal_odd_mark_outside (i j a : Omega) (hij : i ≠ j) (c : golay)
    (ho : integerDot (minimumPairPlus i j).val (oddMinimumVector a c).val = 0) :
    a ≠ i ∧ a ≠ j := by
  have he : (oddMinimumVector a c).val i + (oddMinimumVector a c).val j = 0 := by
    rw [minimumPairPlus_dot] at ho
    omega
  constructor
  · intro ha
    subst a
    have h1 := oddMinimumVector_at_mark i c
    have h2 := oddMinimumVector_off_mark i j c hij.symm
    omega
  · intro ha
    subst a
    have h1 := oddMinimumVector_at_mark j c
    have h2 := oddMinimumVector_off_mark j i c hij
    omega

end Atlas.Conway
