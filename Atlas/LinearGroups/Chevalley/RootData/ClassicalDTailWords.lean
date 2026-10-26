import Atlas.LinearGroups.Chevalley.RootData.ClassicalDTailCoordinates
import Atlas.LinearGroups.Chevalley.RootData.ParabolicWordReduction

/-! Transport of actual D words to the tail parabolic. A D root is never
silently replaced by a coordinate axis: two actual roots sum to twice each
axis, and cancellation occurs only in the torsion-free integer lattice. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDTail
open Classical ClassicalData RootData

def latticeWord (n : ℕ) : List (baseD n).support → Module.End ℤ (ClassicalData.Lattice (n + 2))
  | [] => 1
  | i :: l => ((pairingD (n + 2)).reflection i.val).toLinearMap * latticeWord n l

theorem latticeWord_root (n : ℕ) (l : List (baseD n).support) (a : DRoot (n + 2)) :
    latticeWord n l a.val =
      (simpleReflectionWord (pairingD (n + 2)) (baseD n) l a).val := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change reflect i.val (latticeWord n l a.val) =
      reflect i.val (simpleReflectionWord (pairingD (n + 2)) (baseD n) l a).val
    rw [ih]

/-- Actual D root values determine an integral linear map. The coordinate
basis is recovered from (e_i+e_j)+(e_i−e_j)=2e_i, including rank two. -/
theorem linearMap_eq_of_root_values (n : ℕ)
    (f g : Module.End ℤ (ClassicalData.Lattice (n + 2)))
    (h : ∀ a : DRoot (n + 2), f a.val = g a.val) : f = g := by
  apply (Pi.basisFun ℤ (Fin (n + 2))).ext
  intro i
  rw [Pi.basisFun_apply]
  obtain ⟨j, hji⟩ := exists_ne i
  let a := longRoot false i j (Ne.symm hji) 1 1 (Or.inl rfl) (Or.inl rfl)
  let d := longRoot false i j (Ne.symm hji) 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have hsum : a.val + d.val = (2 : ℤ) • (Pi.single i 1 : ClassicalData.Lattice (n + 2)) := by
    ext k
    simp only [a, d, longRoot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    split_ifs <;> ring
  have he := congrArg₂ (fun x y : ClassicalData.Lattice (n + 2) => x + y) (h a) (h d)
  rw [← map_add, ← map_add, hsum, map_smul, map_smul] at he
  funext k
  have hk := congrFun he k
  simp only [Pi.smul_apply, smul_eq_mul] at hk
  omega

theorem latticeWord_eq_of_rootWord_eq (n : ℕ) (l r : List (baseD n).support)
    (h : rootWeylWord (pairingD (n + 2)) (baseD n) l =
      rootWeylWord (pairingD (n + 2)) (baseD n) r) : latticeWord n l = latticeWord n r := by
  apply linearMap_eq_of_root_values n
  intro a
  rw [latticeWord_root, latticeWord_root]
  simpa only [rootWeylWord_val] using
    congrArg (fun w : W n => (w.val a).val) h

theorem latticeWord_tail (n : ℕ) (l : List (baseD n).support)
    (t : ℤ) (x : ClassicalData.Lattice (n + 2)) :
    latticeWord (n + 1) (l.map (tailSimple n)) (Fin.cons t x) =
      Fin.cons t (latticeWord n l x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change reflect (tailSimple n i).val
      (latticeWord (n + 1) (l.map (tailSimple n)) (Fin.cons t x)) = _
    rw [ih, tailSimple_val, tailRoot_reflect_cons]
    rfl

/-- Word independence uses equality of the actual integral actions. -/
theorem tail_rootWord_eq_of_eq (n : ℕ) (l r : List (baseD n).support)
    (h : rootWeylWord (pairingD (n + 2)) (baseD n) l =
      rootWeylWord (pairingD (n + 2)) (baseD n) r) :
    rootWeylWord (pairingD (n + 3)) (baseD (n + 1)) (l.map (tailSimple n)) =
      rootWeylWord (pairingD (n + 3)) (baseD (n + 1)) (r.map (tailSimple n)) := by
  apply Subtype.ext
  rw [rootWeylWord_val, rootWeylWord_val]
  apply Equiv.ext
  intro a
  apply Subtype.ext
  rw [← latticeWord_root, ← latticeWord_root, ← Fin.cons_self_tail a.val,
    latticeWord_tail, latticeWord_tail, latticeWord_eq_of_rootWord_eq n l r h]

theorem tail_rootWord_root (n : ℕ) (l : List (baseD n).support) (a : DRoot (n + 2)) :
    (rootWeylWord (pairingD (n + 3)) (baseD (n + 1)) (l.map (tailSimple n))).val
        (tailRoot a) =
      tailRoot ((rootWeylWord (pairingD (n + 2)) (baseD n) l).val a) := by
  rw [rootWeylWord_val, rootWeylWord_val]
  apply Subtype.ext
  change (simpleReflectionWord (pairingD (n + 3)) (baseD (n + 1))
    (l.map (tailSimple n)) (tailRoot a)).val =
      Fin.cons 0 (simpleReflectionWord (pairingD (n + 2)) (baseD n) l a).val
  rw [← latticeWord_root]
  change latticeWord (n + 1) (l.map (tailSimple n)) (Fin.cons 0 a.val) = _
  rw [latticeWord_tail, latticeWord_root]

theorem tailWord_surjective_of_letters (n : ℕ) (l : List (baseD (n + 1)).support)
    (hl : ∀ i ∈ l, i ∈ ClassicalDParabolic.J n) :
    ∃ r : List (baseD n).support, r.map (tailSimple n) = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons i l ih =>
    obtain ⟨j, hj⟩ := (tailSimple_range n i).mp (hl i List.mem_cons_self)
    obtain ⟨r, hr⟩ := ih (fun k hk => hl k (List.mem_cons_of_mem i hk))
    exact ⟨j :: r, by rw [List.map_cons, hj, hr]⟩

end Atlas.Chevalley.ClassicalDTail
