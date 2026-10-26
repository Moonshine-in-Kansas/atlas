import Atlas.LinearGroups.Chevalley.RootData.TypeARootHeight
import Atlas.LinearGroups.Chevalley.RootData.DominantFunctionalStabilizer

/-! The first-coordinate stabilizer is the actual zero-wall parabolic of type A.
This is a uniform stabilizer identification, not a count of the Weyl group. -/
noncomputable section
namespace Atlas.Chevalley.TypeAData
open Classical RootData

def firstCoordinateFunctional (r : ℕ) :
    (pairing (r + 2)).rootSpan ℤ →+ ℚ where
  toFun x := (x.val 0 : ℚ)
  map_zero' := by simp
  map_add' x y := by simp

theorem firstCoordinateFunctional_simple (r : ℕ) (i : Fin (r + 1)) :
    firstCoordinateFunctional r
      ((pairing (r + 2)).rootSpanMem ℤ (baseIndexEquiv (r + 1) i).val) =
        if i = 0 then 1 else 0 := by
  have hsucc : (0 : Fin (r + 2)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  have hcast : (0 : Fin (r + 2)) = i.castSucc ↔ i = 0 := by
    constructor
    · intro h
      apply Fin.ext
      exact (congrArg Fin.val h).symm
    · intro h
      subst i
      rfl
  change ((((Pi.single i.castSucc (1 : ℤ) : Lattice (r + 2)) 0) -
    (Pi.single i.succ (1 : ℤ) : Lattice (r + 2)) 0 : ℤ) : ℚ) = _
  simp only [Pi.single_apply, if_neg hsucc, hcast, sub_zero]
  split_ifs <;> norm_num

theorem firstCoordinateFunctional_nonneg (r : ℕ) (i : (base (r + 1)).support) :
    0 ≤ firstCoordinateFunctional r ((pairing (r + 2)).rootSpanMem ℤ i.val) := by
  obtain ⟨j, rfl⟩ := (baseIndexEquiv (r + 1)).surjective i
  rw [firstCoordinateFunctional_simple]
  split_ifs <;> norm_num

/-- The zero walls are exactly all simple nodes other than the first. -/
theorem firstCoordinate_zero_simple_iff (r : ℕ) (i : Fin (r + 1)) :
    baseIndexEquiv (r + 1) i ∈
      rootFunctionalZeroSimple (pairing (r + 2)) (base (r + 1))
        (firstCoordinateFunctional r) ↔ i ≠ 0 := by
  simp only [rootFunctionalZeroSimple, Finset.mem_filter, Finset.mem_univ,
    true_and, firstCoordinateFunctional_simple]
  split_ifs <;> simp_all

/-- Literal coordinate stabilizer equals the actual parabolic subgroup W(A_r). -/
theorem coordinateWeyl_mem_zero_parabolic_iff (r : ℕ)
    (e : Equiv.Perm (Fin (r + 2))) :
    coordinateWeylEquiv (r + 2) e ∈
      rootParabolicSubgroup (pairing (r + 2)) (base (r + 1))
        (rootFunctionalZeroSimple (pairing (r + 2)) (base (r + 1))
          (firstCoordinateFunctional r)) ↔ e 0 = 0 := by
  rw [← rootFunctionalStabilizer_eq_parabolic (pairing (r + 2)) (base (r + 1))
    (firstCoordinateFunctional r) (firstCoordinateFunctional_nonneg r)]
  change (∀ a : Root (r + 2),
    (root (permute e a) 0 : ℚ) = (root a 0 : ℚ)) ↔ e 0 = 0
  constructor
  · intro h
    by_contra he
    have hj : e.symm 0 ≠ 0 := by
      intro hj
      have hh := e.apply_symm_apply 0
      rw [hj] at hh
      exact he hh
    let a : Root (r + 2) := ⟨(0, e.symm 0), hj.symm⟩
    have ha := h a
    have hsecond : (permute e a).val.2 = 0 := e.apply_symm_apply 0
    have hleft : root (permute e a) 0 = -1 := by
      rw [← hsecond]
      exact root_second _
    have hright : root a 0 = 1 := root_first a
    rw [hleft, hright] at ha
    norm_num at ha
  · intro he a
    exact congrArg (fun z : ℤ => (z : ℚ)) (by
      simpa only [he] using root_permute e a 0)

end Atlas.Chevalley.TypeAData
