import Atlas.LinearGroups.Chevalley.RootData.ClassicalBTailCoordinates
import Atlas.LinearGroups.Chevalley.RootData.ParabolicWordReduction

/-! Actual tail-word transport. Equality of root permutations gives equality
of the integral linear maps because every coordinate basis vector is a B
root. This proves word independence without an abstract presentation. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalBParabolic
open Classical ClassicalData RootData

/-- Integral linear action of a literal word in the existing simple reflections. -/
def latticeWord (n : ℕ) : List (baseB n).support → Module.End ℤ (ClassicalData.Lattice (n + 1))
  | [] => 1
  | i :: l => ((pairingB (n + 1)).reflection i.val).toLinearMap * latticeWord n l

theorem latticeWord_root (n : ℕ) (l : List (baseB n).support) (a : BRoot (n + 1)) :
    latticeWord n l a.val =
      (simpleReflectionWord (pairingB (n + 1)) (baseB n) l a).val := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change reflect i.val (latticeWord n l a.val) =
      reflect i.val (simpleReflectionWord (pairingB (n + 1)) (baseB n) l a).val
    rw [ih]

/-- Every coordinate vector is an actual short root, so the label action
determines the entire integral linear map. -/
theorem latticeWord_eq_of_rootWord_eq (n : ℕ) (l r : List (baseB n).support)
    (h : rootWeylWord (pairingB (n + 1)) (baseB n) l =
      rootWeylWord (pairingB (n + 1)) (baseB n) r) : latticeWord n l = latticeWord n r := by
  apply (Pi.basisFun ℤ (Fin (n + 1))).ext
  intro i
  rw [Pi.basisFun_apply]
  change latticeWord n l (shortRoot i 1 (Or.inl rfl)).val =
    latticeWord n r (shortRoot i 1 (Or.inl rfl)).val
  rw [latticeWord_root, latticeWord_root]
  simpa only [rootWeylWord_val] using
    congrArg (fun w : W n => (w.val (shortRoot i 1 (Or.inl rfl))).val) h

/-- Tail words fix the first coordinate and implement the lower-rank word
on every remaining coordinate, not just on a selected orbit. -/
theorem latticeWord_tail (n : ℕ) (l : List (baseB n).support)
    (t : ℤ) (x : ClassicalData.Lattice (n + 1)) :
    latticeWord (n + 1) (l.map (tailSimple n)) (Fin.cons t x) =
      Fin.cons t (latticeWord n l x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change reflect (tailSimple n i).val
      (latticeWord (n + 1) (l.map (tailSimple n)) (Fin.cons t x)) = _
    rw [ih, tailSimple_val, tailRoot_reflect_cons]
    rfl

/-- Word independence in the actual larger Weyl image follows from the
integral coordinate calculation, not from a supplied Coxeter relation. -/
theorem tail_rootWord_eq_of_eq (n : ℕ) (l r : List (baseB n).support)
    (h : rootWeylWord (pairingB (n + 1)) (baseB n) l =
      rootWeylWord (pairingB (n + 1)) (baseB n) r) :
    rootWeylWord (pairingB (n + 2)) (baseB (n + 1)) (l.map (tailSimple n)) =
      rootWeylWord (pairingB (n + 2)) (baseB (n + 1)) (r.map (tailSimple n)) := by
  apply Subtype.ext
  rw [rootWeylWord_val, rootWeylWord_val]
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rw [← latticeWord_root, ← latticeWord_root, ← Fin.cons_self_tail a.val,
    latticeWord_tail, latticeWord_tail, latticeWord_eq_of_rootWord_eq n l r h]

theorem tail_rootWord_root (n : ℕ) (l : List (baseB n).support) (a : BRoot (n + 1)) :
    (rootWeylWord (pairingB (n + 2)) (baseB (n + 1)) (l.map (tailSimple n))).val
        (tailRoot a) =
      tailRoot ((rootWeylWord (pairingB (n + 1)) (baseB n) l).val a) := by
  rw [rootWeylWord_val, rootWeylWord_val]
  apply Subtype.ext
  change (simpleReflectionWord (pairingB (n + 2)) (baseB (n + 1))
    (l.map (tailSimple n)) (tailRoot a)).val =
      Fin.cons 0 (simpleReflectionWord (pairingB (n + 1)) (baseB n) l a).val
  rw [← latticeWord_root]
  change latticeWord (n + 1) (l.map (tailSimple n)) (Fin.cons 0 a.val) = _
  rw [latticeWord_tail, latticeWord_root]

/-- Every word with letters in the actual first-node parabolic is literally
the shift of a lower-rank word. -/
theorem tailWord_surjective_of_letters (n : ℕ) (l : List (baseB (n + 1)).support)
    (hl : ∀ i ∈ l, i ∈ J (n + 1)) :
    ∃ r : List (baseB n).support, r.map (tailSimple n) = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons i l ih =>
    obtain ⟨j, hj⟩ := (tailSimple_range n i).mp (hl i List.mem_cons_self)
    obtain ⟨r, hr⟩ := ih (fun k hk => hl k (List.mem_cons_of_mem i hk))
    exact ⟨j :: r, by rw [List.map_cons, hj, hr]⟩

end Atlas.Chevalley.ClassicalBParabolic
