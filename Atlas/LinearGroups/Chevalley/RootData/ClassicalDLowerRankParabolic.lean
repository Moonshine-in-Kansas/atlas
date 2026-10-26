import Atlas.LinearGroups.Chevalley.RootData.ClassicalDTailWords

/-! The actual first-node type-D parabolic is the lower-rank Weyl image,
with exactly the same intrinsic and ambient shortest simple-word lengths. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDTail
open Classical ClassicalData RootData

private def shortestWord (n : ℕ) (w : W n) : List (baseD n).support :=
  (rootWeylLength_spec (pairingD (n + 2)) (baseD n) w).choose

private theorem shortestWord_length (n : ℕ) (w : W n) :
    (shortestWord n w).length = rootWeylLength (pairingD (n + 2)) (baseD n) w :=
  (rootWeylLength_spec (pairingD (n + 2)) (baseD n) w).choose_spec.1

private theorem shortestWord_eval (n : ℕ) (w : W n) :
    rootWeylWord (pairingD (n + 2)) (baseD n) (shortestWord n w) = w := by
  apply Subtype.ext
  rw [rootWeylWord_val]
  exact (rootWeylLength_spec (pairingD (n + 2)) (baseD n) w).choose_spec.2

/-- Extend the actual lower-rank integral Weyl action by fixing the first coordinate. -/
def tailWeylHom (n : ℕ) : W n →* W (n + 1) where
  toFun w := rootWeylWord (pairingD (n + 3)) (baseD (n + 1))
    ((shortestWord n w).map (tailSimple n))
  map_one' := by
    have h := tail_rootWord_eq_of_eq n (shortestWord n 1) [] (shortestWord_eval n 1)
    exact h
  map_mul' w v := by
    have he : rootWeylWord (pairingD (n + 2)) (baseD n) (shortestWord n (w * v)) =
        rootWeylWord (pairingD (n + 2)) (baseD n) (shortestWord n w ++ shortestWord n v) := by
      rw [rootWeylWord_append, shortestWord_eval, shortestWord_eval, shortestWord_eval]
    have h := tail_rootWord_eq_of_eq n _ _ he
    simpa only [List.map_append, rootWeylWord_append] using h

@[simp] theorem tailWeylHom_word (n : ℕ) (l : List (baseD n).support) :
    tailWeylHom n (rootWeylWord (pairingD (n + 2)) (baseD n) l) =
      rootWeylWord (pairingD (n + 3)) (baseD (n + 1)) (l.map (tailSimple n)) := by
  exact tail_rootWord_eq_of_eq n _ l (shortestWord_eval n _)

/-- This is literal intertwining on the embedded original integer root labels. -/
theorem tailWeylHom_root (n : ℕ) (w : W n) (a : DRoot (n + 2)) :
    (tailWeylHom n w).val (tailRoot a) = tailRoot (w.val a) := by
  change (rootWeylWord (pairingD (n + 3)) (baseD (n + 1))
    ((shortestWord n w).map (tailSimple n))).val (tailRoot a) = _
  rw [tail_rootWord_root, shortestWord_eval]

theorem tailWeylHom_injective (n : ℕ) : Function.Injective (tailWeylHom n) := by
  intro w v h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  apply tailRoot_injective (n + 2)
  simpa only [tailWeylHom_root] using congrArg (fun z : W (n + 1) => z.val (tailRoot a)) h

theorem tailWeylHom_mem (n : ℕ) (w : W n) :
    tailWeylHom n w ∈ rootParabolicSubgroup (pairingD (n + 3)) (baseD (n + 1)) (ClassicalDParabolic.J n) := by
  apply rootWeylWord_mem_parabolic
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact tailSimple_mem n j

/-- Equality with the actual standard parabolic, proved using its generated words. -/
theorem tailWeylHom_range (n : ℕ) :
    (tailWeylHom n).range = rootParabolicSubgroup (pairingD (n + 3))
      (baseD (n + 1)) (ClassicalDParabolic.J n) := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact tailWeylHom_mem n v
  · intro hw
    obtain ⟨l, hl, he⟩ := (rootParabolic_mem_iff_word (pairingD (n + 3))
      (baseD (n + 1)) (ClassicalDParabolic.J n) w).mp hw
    obtain ⟨r, hr⟩ := tailWord_surjective_of_letters n l hl
    refine ⟨rootWeylWord (pairingD (n + 2)) (baseD n) r, ?_⟩
    rw [tailWeylHom_word, hr, he]

def lowerRankParabolicEquiv (n : ℕ) : W n ≃*
    rootParabolicSubgroup (pairingD (n + 3)) (baseD (n + 1)) (ClassicalDParabolic.J n) :=
  (MonoidHom.ofInjective (tailWeylHom_injective n)).trans
    (MulEquiv.subgroupCongr (tailWeylHom_range n))

/-- Intrinsic length agrees exactly with ambient length. The reverse bound
uses a reduced word retaining the parabolic letters, not an order argument. -/
theorem tailWeylHom_length (n : ℕ) (w : W n) :
    rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) (tailWeylHom n w) =
      rootWeylLength (pairingD (n + 2)) (baseD n) w := by
  apply Nat.le_antisymm
  · have hb := rootWeylWord_length_le (pairingD (n + 3)) (baseD (n + 1))
      ((shortestWord n w).map (tailSimple n))
    change rootWeylLength (pairingD (n + 3)) (baseD (n + 1))
      (rootWeylWord (pairingD (n + 3)) (baseD (n + 1))
        ((shortestWord n w).map (tailSimple n))) ≤ _
    simpa only [List.length_map, shortestWord_length] using hb
  · obtain ⟨l, hl, he, hred⟩ := rootParabolic_exists_reduced_word
      (pairingD (n + 3)) (baseD (n + 1)) (ClassicalDParabolic.J n)
      (tailWeylHom n w) (tailWeylHom_mem n w)
    obtain ⟨r, hr⟩ := tailWord_surjective_of_letters n l hl
    have hrw : rootWeylWord (pairingD (n + 2)) (baseD n) r = w := by
      apply tailWeylHom_injective n
      rw [tailWeylHom_word, hr, he]
    have hb := rootWeylWord_length_le (pairingD (n + 2)) (baseD n) r
    have hlen : r.length = l.length := by
      simpa only [List.length_map] using congrArg List.length hr
    change rootWeylLength (pairingD (n + 3)) (baseD (n + 1))
      (rootWeylWord (pairingD (n + 3)) (baseD (n + 1)) l) = l.length at hred
    rw [he] at hred
    rw [hrw, hlen, ← hred] at hb
    exact hb

theorem lowerRankParabolicEquiv_length (n : ℕ) (w : W n) :
    rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) (lowerRankParabolicEquiv n w).val =
      rootWeylLength (pairingD (n + 2)) (baseD n) w :=
  tailWeylHom_length n w

end Atlas.Chevalley.ClassicalDTail
