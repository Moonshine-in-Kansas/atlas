import Atlas.LinearGroups.Chevalley.RootData.TypeAParabolicStabilizer
import Atlas.LinearGroups.Chevalley.RootData.ParabolicCosetDecomposition
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Fin.Basic

/-! The actual type-A minimal right-parabolic representatives, indexed by
the image of coordinate zero. These are the increasing insertions, not swaps. -/
noncomputable section
namespace Atlas.Chevalley.TypeAData
open Classical RootData

abbrev firstZeroWalls (r : ℕ) :=
  rootFunctionalZeroSimple (pairing (r + 2)) (base (r + 1))
    (firstCoordinateFunctional r)

def coordinateRepresentative (r : ℕ) (k : Fin (r + 2)) :
    (pairing (r + 2)).weylGroupToPerm.range :=
  coordinateWeylEquiv (r + 2) k.cycleRange.symm

theorem coordinateRepresentative_minimal (r : ℕ) (k : Fin (r + 2)) :
    ∀ i ∈ firstZeroWalls r, (base (r + 1)).IsPos
      ((coordinateRepresentative r k).val i.val) := by
  intro i hi
  obtain ⟨j, rfl⟩ := (baseIndexEquiv (r + 1)).surjective i
  have hj : j ≠ 0 := (firstCoordinate_zero_simple_iff r j).mp hi
  rw [isPos_iff_coordinate_lt]
  change k.cycleRange.symm j.castSucc < k.cycleRange.symm j.succ
  let p : Fin (r + 1) := ⟨j.val - 1, by omega⟩
  have hp : p.succ = j.castSucc := by
    apply Fin.ext
    have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    change j.val - 1 + 1 = j.val
    omega
  rw [← hp, Fin.cycleRange_symm_succ, Fin.cycleRange_symm_succ]
  apply Fin.strictMono_succAbove k
  have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
  change j.val - 1 < j.val
  omega

def coordinateRepresentativeMap (r : ℕ) : Fin (r + 2) →
    rootParabolicRepresentatives (pairing (r + 2)) (base (r + 1)) (firstZeroWalls r) :=
  fun k => ⟨coordinateRepresentative r k, coordinateRepresentative_minimal r k⟩

theorem coordinateRepresentativeMap_bijective (r : ℕ) :
    Function.Bijective (coordinateRepresentativeMap r) := by
  constructor
  · intro k l h
    have he := congrArg (fun x : rootParabolicRepresentatives (pairing (r + 2))
      (base (r + 1)) (firstZeroWalls r) =>
        (coordinateWeylEquiv (r + 2)).symm x.val 0) h
    simpa only [coordinateRepresentativeMap, coordinateRepresentative,
      MulEquiv.symm_apply_apply, Fin.cycleRange_symm_zero] using he
  · intro x
    let e := (coordinateWeylEquiv (r + 2)).symm x.val
    let k := e 0
    have he : coordinateWeylEquiv (r + 2) e = x.val :=
      (coordinateWeylEquiv (r + 2)).apply_symm_apply x.val
    have hfix : (k.cycleRange * e) 0 = 0 := by
      change k.cycleRange k = 0
      exact Fin.cycleRange_self k
    have hm := (coordinateWeyl_mem_zero_parabolic_iff r (k.cycleRange * e)).mpr hfix
    have heq : coordinateWeylEquiv (r + 2) (k.cycleRange * e) =
        (coordinateRepresentative r k)⁻¹ * x.val := by
      rw [map_mul, he]
      congr 1
    rw [heq] at hm
    have hx := rootWeyl_parabolic_minimal_unique (pairing (r + 2)) (base (r + 1))
      (firstZeroWalls r) (coordinateRepresentative r k) x.val
      (coordinateRepresentative_minimal r k) x.property hm
    exact ⟨k, Subtype.ext hx⟩

def coordinateRepresentativeEquiv (r : ℕ) : Fin (r + 2) ≃
    rootParabolicRepresentatives (pairing (r + 2)) (base (r + 1)) (firstZeroWalls r) :=
  Equiv.ofBijective (coordinateRepresentativeMap r) (coordinateRepresentativeMap_bijective r)

private theorem representative_inversion_iff (r : ℕ) (k : Fin (r + 2))
    (a : Root (r + 2)) :
    (a.val.1 < a.val.2 ∧ k.cycleRange.symm a.val.2 < k.cycleRange.symm a.val.1) ↔
      a.val.1 = 0 ∧ a.val.2.val ≤ k.val := by
  rcases a with ⟨⟨a, b⟩, hab⟩
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => exact False.elim (hab rfl)
    | succ b =>
      simp only [Fin.succ_pos, true_and, Fin.cycleRange_symm_zero,
        Fin.cycleRange_symm_succ, Fin.succAbove_lt_iff_castSucc_lt]
      change b.val < k.val ↔ b.val + 1 ≤ k.val
      omega
  | succ a =>
    cases b using Fin.cases with
    | zero => simp
    | succ b =>
      simp only [Fin.succ_lt_succ_iff, Fin.cycleRange_symm_succ,
        (Fin.strictMono_succAbove k).lt_iff_lt, Fin.succ_ne_zero, false_and, iff_false]
      omega

/-- There are exactly k inversions in the increasing insertion at coordinate k. -/
theorem coordinateRepresentative_length (r : ℕ) (k : Fin (r + 2)) :
    rootWeylLength (pairing (r + 2)) (base (r + 1)) (coordinateRepresentative r k) =
      k.val := by
  rw [coordinateRepresentative, coordinateWeylEquiv_length]
  simp_rw [representative_inversion_iff]
  have hc : (Finset.univ : Finset (Fin k.val)).card =
      (Finset.univ.filter (fun a : Root (r + 2) =>
        a.val.1 = 0 ∧ a.val.2.val ≤ k.val)).card := by
    let f : Fin k.val → Root (r + 2) := fun t =>
      ⟨(0, ⟨t.val + 1, by omega⟩), by intro h; have hv := congrArg Fin.val h; simp at hv⟩
    apply Finset.card_bij (fun t _ => f t)
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨rfl, by change t.val + 1 ≤ k.val; omega⟩
    · intro t ht u hu h
      apply Fin.ext
      have hv := congrArg (fun a : Root (r + 2) => a.val.2.val) h
      change t.val + 1 = u.val + 1 at hv
      omega
    · intro a ha
      obtain ⟨hfirst, hsecond⟩ := (Finset.mem_filter.mp ha).2
      have hn : a.val.2.val ≠ 0 := by
        intro hz
        exact a.property (hfirst.trans (Fin.ext hz).symm)
      let t : Fin k.val := ⟨a.val.2.val - 1, by omega⟩
      refine ⟨t, Finset.mem_univ t, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact hfirst.symm
      · apply Fin.ext
        change a.val.2.val - 1 + 1 = a.val.2.val
        omega
  simpa using hc.symm

theorem coordinateRepresentativeEquiv_length (r : ℕ) (k : Fin (r + 2)) :
    rootWeylLength (pairing (r + 2)) (base (r + 1))
      (coordinateRepresentativeEquiv r k).val = k.val :=
  coordinateRepresentative_length r k

end Atlas.Chevalley.TypeAData
