import Atlas.LinearGroups.Chevalley.RootData.ClassicalDParabolicFunctional
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-! Literal zero-first-coordinate inclusion of D roots, preserving the two
fork nodes even for the D₂→D₃ base. These are actual integer-coordinate maps. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDTail
open Classical ClassicalData RootData

abbrev W (n : ℕ) := (pairingD (n + 2)).weylGroupToPerm.range

def tailLattice (r : ℕ) : ClassicalData.Lattice r →ₗ[ℤ] ClassicalData.Lattice (r + 1) where
  toFun x := Fin.cons 0 x
  map_add' x y := by funext k; cases k using Fin.cases <;> simp
  map_smul' a x := by funext k; cases k using Fin.cases <;> simp

@[simp] theorem tailLattice_zero (r : ℕ) (x : ClassicalData.Lattice r) : tailLattice r x 0 = 0 := rfl
@[simp] theorem tailLattice_succ (r : ℕ) (x : ClassicalData.Lattice r) (i : Fin r) :
    tailLattice r x i.succ = x i := rfl

theorem tailLattice_injective (r : ℕ) : Function.Injective (tailLattice r) := by
  intro x y h
  funext i
  exact congrFun h i.succ

@[simp] theorem dot_cons (r : ℕ) (s t : ℤ) (x y : ClassicalData.Lattice r) :
    dot (Fin.cons s x) (Fin.cons t y) = s * t + dot x y := by
  simp only [dot, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

@[simp] theorem tailLattice_dot (r : ℕ) (x y : ClassicalData.Lattice r) :
    dot (tailLattice r x) (tailLattice r y) = dot x y := by
  change dot (Fin.cons 0 x) (Fin.cons 0 y) = _
  rw [dot_cons, zero_mul, zero_add]

def tailRoot {r : ℕ} (a : DRoot r) : DRoot (r + 1) :=
  ⟨tailLattice r a.val, by simpa only [tailLattice_dot] using a.property⟩

theorem tailRoot_injective (r : ℕ) : Function.Injective (@tailRoot r) := by
  intro a b h
  apply Subtype.ext
  exact tailLattice_injective r (congrArg Subtype.val h)

@[simp] theorem tailRoot_scale {r : ℕ} (a : DRoot r) :
    corootScale (tailRoot a) = corootScale a := by
  simp only [corootScale, tailRoot, tailLattice_dot]

theorem tailRoot_reflect_cons {r : ℕ} (a : DRoot r) (t : ℤ) (x : ClassicalData.Lattice r) :
    reflect (tailRoot a) (Fin.cons t x) = Fin.cons t (reflect a x) := by
  have hd : dot (tailRoot a).val (Fin.cons t x) = dot a.val x := by
    change dot (Fin.cons 0 a.val) (Fin.cons t x) = _
    rw [dot_cons, zero_mul, zero_add]
  funext k
  simp only [reflect, tailRoot_scale, hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  cases k using Fin.cases <;>
    simp only [Fin.cons_zero, Fin.cons_succ, tailRoot, tailLattice_zero,
      tailLattice_succ, mul_zero, sub_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem tailRoot_reflection {r : ℕ} (a b : DRoot r) :
    (pairingD (r + 1)).reflectionPerm (tailRoot a) (tailRoot b) =
      tailRoot ((pairingD r).reflectionPerm a b) := by
  apply Subtype.ext
  exact tailRoot_reflect_cons a 0 b.val

private theorem tailLattice_single {r : ℕ} (i : Fin r) (t : ℤ) :
    tailLattice r (Pi.single i t) = (Pi.single i.succ t : ClassicalData.Lattice (r + 1)) := by
  funext k
  cases k using Fin.cases <;> simp [Pi.single_apply]

/-- Both smaller fork roots map to the corresponding larger fork roots. -/
theorem tailRoot_simple (n : ℕ) (i : Fin (n + 2)) :
    tailRoot (simpleD n i) = simpleD (n + 1) i.succ := by
  apply Subtype.ext
  change tailLattice (n + 2) (simpleD n i).val = (simpleD (n + 1) i.succ).val
  rw [simpleD_vector, simpleD_vector]
  by_cases hi : i.val = n + 1
  · have hs : i.succ.val = n + 1 + 1 := by simp only [Fin.val_succ]; omega
    simp only [hi, hs, dite_true, map_add, tailLattice_single]
    all_goals rfl
  · have hs : i.succ.val ≠ n + 1 + 1 := by simp only [Fin.val_succ]; omega
    simp only [hi, hs, dite_false, map_sub, tailLattice_single]
    all_goals rfl

def tailSimple (n : ℕ) (i : (baseD n).support) : (baseD (n + 1)).support :=
  baseDIndexEquiv (n + 1) (((baseDIndexEquiv n).symm i).succ)

@[simp] theorem tailSimple_val (n : ℕ) (i : (baseD n).support) :
    (tailSimple n i).val = tailRoot i.val := by
  obtain ⟨k, rfl⟩ := (baseDIndexEquiv n).surjective i
  simp only [tailSimple, Equiv.symm_apply_apply]
  change simpleD (n + 1) k.succ = tailRoot (simpleD n k)
  exact (tailRoot_simple n k).symm

theorem tailSimple_mem (n : ℕ) (i : (baseD n).support) :
    tailSimple n i ∈ ClassicalDParabolic.J n := by
  simp only [ClassicalDParabolic.J, Finset.mem_erase, Finset.mem_univ, and_true]
  intro h
  have he := (baseDIndexEquiv (n + 1)).injective h
  exact Fin.succ_ne_zero _ he

theorem tailSimple_range (n : ℕ) (i : (baseD (n + 1)).support) :
    i ∈ ClassicalDParabolic.J n ↔ ∃ j, tailSimple n j = i := by
  constructor
  · intro hi
    let k := (baseDIndexEquiv (n + 1)).symm i
    have hk : k ≠ 0 := by
      intro h
      have he : i = baseDIndexEquiv (n + 1) 0 := by
        rw [← (baseDIndexEquiv (n + 1)).apply_symm_apply i]
        exact congrArg (baseDIndexEquiv (n + 1)) h
      exact (Finset.mem_erase.mp hi).1 he
    refine ⟨baseDIndexEquiv n (k.pred hk), ?_⟩
    simp only [tailSimple, Equiv.symm_apply_apply, Fin.succ_pred]
    exact (baseDIndexEquiv (n + 1)).apply_symm_apply i
  · rintro ⟨j, rfl⟩
    exact tailSimple_mem n j

end Atlas.Chevalley.ClassicalDTail
