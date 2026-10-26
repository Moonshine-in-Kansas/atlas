import Atlas.LinearGroups.Chevalley.RootData.ClassicalBParabolicOrbit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-! The literal zero-first-coordinate embedding of integral B roots and its
compatibility with actual root reflections and the pinned simple chain. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalBParabolic
open Classical ClassicalData RootData

/-- Actual integral coordinate inclusion; no abstract root-datum equivalence is used. -/
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

/-- The root is embedded by its literal integer coordinates, preserving its length. -/
def tailRoot {r : ℕ} (a : BRoot r) : BRoot (r + 1) :=
  ⟨tailLattice r a.val, by simpa only [tailLattice_dot] using a.property⟩

theorem tailRoot_injective (r : ℕ) : Function.Injective (@tailRoot r) := by
  intro a b h
  apply Subtype.ext
  exact tailLattice_injective r (congrArg Subtype.val h)

@[simp] theorem tailRoot_scale {r : ℕ} (a : BRoot r) :
    corootScale (tailRoot a) = corootScale a := by
  simp only [corootScale, tailRoot, tailLattice_dot]

/-- The larger reflection fixes the first coordinate and acts by the smaller
actual reflection on all remaining coordinates, including arbitrary vectors. -/
theorem tailRoot_reflect_cons {r : ℕ} (a : BRoot r) (t : ℤ) (x : ClassicalData.Lattice r) :
    reflect (tailRoot a) (Fin.cons t x) = Fin.cons t (reflect a x) := by
  have hd : dot (tailRoot a).val (Fin.cons t x) = dot a.val x := by
    change dot (Fin.cons 0 a.val) (Fin.cons t x) = _
    rw [dot_cons, zero_mul, zero_add]
  funext k
  simp only [reflect, tailRoot_scale, hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  cases k using Fin.cases <;>
    simp only [Fin.cons_zero, Fin.cons_succ, tailRoot, tailLattice_zero,
      tailLattice_succ, mul_zero, sub_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem tailRoot_reflection {r : ℕ} (a b : BRoot r) :
    (pairingB (r + 1)).reflectionPerm (tailRoot a) (tailRoot b) =
      tailRoot ((pairingB r).reflectionPerm a b) := by
  apply Subtype.ext
  exact tailRoot_reflect_cons a 0 b.val

private theorem tailLattice_single {r : ℕ} (i : Fin r) (t : ℤ) :
    tailLattice r (Pi.single i t) = (Pi.single i.succ t : ClassicalData.Lattice (r + 1)) := by
  funext k
  cases k using Fin.cases <;> simp [Pi.single_apply]

/-- The smaller pinned simple chain is precisely the tail of the larger one. -/
theorem tailRoot_simple (n : ℕ) (i : Fin (n + 1)) :
    tailRoot (simpleB n i) = simpleB (n + 1) i.succ := by
  apply Subtype.ext
  change tailLattice (n + 1) (simpleB n i).val = (simpleB (n + 1) i.succ).val
  rw [simpleB_vector, simpleB_vector]
  by_cases hi : i.val < n
  · have hs : i.succ.val < n + 1 := by simpa only [Fin.val_succ] using Nat.succ_lt_succ hi
    simp only [chainVector, hi, hs, dite_true, map_sub, tailLattice_single]
    congr 2
  · have hs : ¬ i.succ.val < n + 1 := by simp only [Fin.val_succ]; omega
    simp only [chainVector, hi, hs, dite_false, map_smul, tailLattice_single]

/-- Shift a genuine simple-root label, using the existing pinned index equivalences. -/
def tailSimple (n : ℕ) (i : (baseB n).support) : (baseB (n + 1)).support :=
  simple (n + 1) (((baseBIndexEquiv n).symm i).succ)

@[simp] theorem tailSimple_val (n : ℕ) (i : (baseB n).support) :
    (tailSimple n i).val = tailRoot i.val := by
  obtain ⟨k, rfl⟩ := (baseBIndexEquiv n).surjective i
  simp only [tailSimple, Equiv.symm_apply_apply]
  change simpleB (n + 1) k.succ = tailRoot (simpleB n k)
  exact (tailRoot_simple n k).symm

theorem tailSimple_mem (n : ℕ) (i : (baseB n).support) : tailSimple n i ∈ J (n + 1) := by
  simp only [J, Finset.mem_erase, Finset.mem_univ, and_true]
  intro h
  have he := (baseBIndexEquiv (n + 1)).injective h
  exact Fin.succ_ne_zero _ he

theorem tailSimple_range (n : ℕ) (i : (baseB (n + 1)).support) :
    i ∈ J (n + 1) ↔ ∃ j, tailSimple n j = i := by
  constructor
  · intro hi
    let k := (baseBIndexEquiv (n + 1)).symm i
    have hk : k ≠ 0 := by
      intro h
      have he : i = simple (n + 1) 0 := by
        rw [← (baseBIndexEquiv (n + 1)).apply_symm_apply i]
        exact congrArg (baseBIndexEquiv (n + 1)) h
      exact (Finset.mem_erase.mp hi).1 he
    refine ⟨simple n (k.pred hk), ?_⟩
    simp only [tailSimple, simple, Equiv.symm_apply_apply, Fin.succ_pred]
    exact (baseBIndexEquiv (n + 1)).apply_symm_apply i
  · rintro ⟨j, rfl⟩
    exact tailSimple_mem n j

end Atlas.Chevalley.ClassicalBParabolic
