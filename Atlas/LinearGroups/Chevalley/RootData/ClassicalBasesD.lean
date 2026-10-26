import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC

/-! Actual integral D root bases, from rank two onward, with exact Cartan numbering. -/

namespace Atlas.Chevalley.ClassicalData
set_option maxHeartbeats 800000
open Classical

/-- The last D simple root is e_(r-2)+e_(r-1); all earlier ones are differences. -/
def simpleD (n : ℕ) (i : Fin (n + 2)) : DRoot (n + 2) :=
  if h : i.val = n + 1 then
    longRoot false ⟨n, by omega⟩ ⟨n + 1, by omega⟩
      (by intro he; have hv := congrArg Fin.val he; change n = n + 1 at hv; omega) 1 1 (Or.inl rfl) (Or.inl rfl)
  else
    longRoot false i ⟨i.val + 1, by omega⟩
      (by intro he; have hv := congrArg Fin.val he; change i.val = i.val + 1 at hv; omega) 1 (-1) (Or.inl rfl) (Or.inr rfl)

/-- Literal coordinate formula with the Bourbaki/mathlib D node numbering. -/
theorem simpleD_vector (n : ℕ) (i : Fin (n + 2)) :
    (simpleD n i).1 = if h : i.val = n + 1 then
      Pi.single ⟨n, by omega⟩ 1 + Pi.single ⟨n + 1, by omega⟩ 1
    else Pi.single i 1 - Pi.single ⟨i.val + 1, by omega⟩ 1 := by
  unfold simpleD
  split_ifs <;> simp [longRoot, sub_eq_add_neg, Pi.single_neg]

theorem simpleD_coroot (n : ℕ) (i : Fin (n + 2)) :
    coroot (simpleD n i) = functional (simpleD n i).1 := by
  have hn : dot (simpleD n i).1 (simpleD n i).1 = 2 := by
    rcases (simpleD n i).2 with ⟨h, _⟩ | h
    · cases h
    · exact h
  ext x
  simp [corootScale, hn]

/-- Exact pinned D Cartan matrix, including the rank-two disconnected base. -/
theorem simpleD_cartan (n : ℕ) (i j : Fin (n + 2)) :
    coroot (simpleD n j) (simpleD n i).1 = CartanMatrix.D (n + 2) i j := by
  rw [simpleD_coroot, functional_apply, simpleD_vector, simpleD_vector]
  unfold CartanMatrix.D
  simp only [Matrix.of_apply]
  split_ifs <;>
    simp [dot_add_left, dot_add_right, dot_sub_left, dot_sub_right,
      dot_single, dot_single_left, Pi.single_apply, Fin.ext_iff] <;>
    (try split_ifs) <;> simp only [Fin.ext_iff, Fin.le_def, Fin.val_mk] at * <;> omega

/-- Doubled integral D coefficients avoid division by two in the ambient lattice. -/
def dCoefficients (n : ℕ) : Lattice (n + 2) →ₗ[ℤ] Lattice (n + 2) where
  toFun x i := if i.val = n + 1 then ∑ k, x k
    else if i.val = n then 2 * cumulative (n + 1) x i - ∑ k, x k
    else 2 * cumulative (n + 1) x i
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
    split_ifs <;> ring
  map_smul' t x := by
    ext i
    change (if i.val = n + 1 then ∑ k, t * x k
      else if i.val = n then 2 * (cumulative (n + 1)) (t • x) i - ∑ k, t * x k
      else 2 * (cumulative (n + 1)) (t • x) i) = t * _
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    split_ifs <;> ring

theorem dCoefficients_simple (n : ℕ) (j : Fin (n + 2)) :
    dCoefficients n (simpleD n j).1 = (2 : ℤ) • Pi.single j 1 := by
  funext i
  rw [simpleD_vector]
  split_ifs with hj
  · simp [dCoefficients, cumulative, Pi.single_apply, Pi.add_apply,
      Finset.sum_add_distrib]
    (try split_ifs) <;> (try simp only [Fin.ext_iff, Fin.le_def, Fin.val_mk] at *) <;> omega
  · simp [dCoefficients, cumulative, Pi.single_apply, Pi.sub_apply,
      Finset.sum_sub_distrib]
    (try split_ifs) <;> (try simp only [Fin.ext_iff, Fin.le_def, Fin.val_mk] at *) <;> omega

theorem simpleD_independent (n : ℕ) :
    LinearIndependent ℤ (fun i => (simpleD n i).1) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h i
  have hm := congrArg (dCoefficients n) h
  simp only [map_sum, map_smul, dCoefficients_simple] at hm
  have hi := congrFun hm i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hi
  omega

theorem simpleD_injective (n : ℕ) : Function.Injective (simpleD n) := by
  intro i j h
  exact (simpleD_independent n).injective (congrArg Subtype.val h)

theorem simpleD_coroot_independent (n : ℕ) :
    LinearIndependent ℤ (fun i => coroot (simpleD n i)) := by
  apply LinearIndependent.of_comp (functionalCoordinates (n + 2))
  have he : functionalCoordinates (n + 2) ∘ (fun i => coroot (simpleD n i)) =
      (fun i => (simpleD n i).1) := by
    funext i
    simp [Function.comp_def, simpleD_coroot]
  rw [he]
  exact simpleD_independent n

def dPositive (n : ℕ) : AddSubmonoid (Lattice (n + 2)) :=
  AddSubmonoid.closure (Set.range (fun i => (simpleD n i).1))

theorem increasing_mem_dPositive (n : ℕ) (i j : Fin (n + 2)) (h : i ≤ j) :
    Pi.single i (1 : ℤ) - Pi.single j 1 ∈ dPositive n := by
  apply AddSubmonoid.closure_mono _ (TypeAData.increasing_difference_mem i j h)
  rintro _ ⟨k, rfl⟩
  refine ⟨k.castSucc, ?_⟩
  change (simpleD n k.castSucc).val = TypeAData.root (TypeAData.simpleRoot k)
  rw [simpleD_vector]
  have hk : k.val ≠ n + 1 := by omega
  simp [hk, TypeAData.root, TypeAData.simpleRoot]
  congr 2

theorem sum_mem_dPositive (n : ℕ) (i j : Fin (n + 2)) (hij : i ≠ j) :
    Pi.single i (1 : ℤ) + Pi.single j 1 ∈ dPositive n := by
  have aux : ∀ i j : Fin (n + 2), i < j →
      Pi.single i (1 : ℤ) + Pi.single j 1 ∈ dPositive n := by
    intro i j hlt
    let p : Fin (n + 2) := ⟨n, by omega⟩
    let q : Fin (n + 2) := ⟨n + 1, by omega⟩
    have hip : i ≤ p := by change i.val ≤ n; have := j.isLt; change i.val < j.val at hlt; omega
    have hjq : j ≤ q := by change j.val ≤ n + 1; omega
    have hi := increasing_mem_dPositive n i p hip
    have hj := increasing_mem_dPositive n j q hjq
    have hlast : Pi.single p (1 : ℤ) + Pi.single q 1 ∈ dPositive n := by
      have hs : (simpleD n q).1 ∈ dPositive n := AddSubmonoid.subset_closure ⟨q, rfl⟩
      simpa [simpleD_vector, p, q] using hs
    have hh := AddSubmonoid.add_mem _ (AddSubmonoid.add_mem _ hi hj) hlast
    convert hh using 1 <;> ext k <;> simp only [Pi.add_apply, Pi.sub_apply] <;> ring
  rcases lt_or_gt_of_ne hij with h | h
  · exact aux i j h
  · simpa only [add_comm] using aux j i h

theorem root_mem_dPositive (n : ℕ) (a : DRoot (n + 2)) :
    a.1 ∈ dPositive n ∨ -a.1 ∈ dPositive n := by
  rcases signed_support_classification a with ⟨h, _⟩ | ⟨i, j, hij, s, t, hs, ht, ha⟩
  · cases h
  · rw [ha]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Or.inl (sum_mem_dPositive n i j hij)
    · rcases le_total i j with h | h
      · left; simpa [Pi.single_neg, sub_eq_add_neg] using increasing_mem_dPositive n i j h
      · right; simpa [Pi.single_neg, sub_eq_add_neg, neg_add_rev, add_comm] using increasing_mem_dPositive n j i h
    · rcases le_total j i with h | h
      · left; simpa [Pi.single_neg, sub_eq_add_neg, add_comm] using increasing_mem_dPositive n j i h
      · right; simpa [Pi.single_neg, sub_eq_add_neg, neg_add_rev, add_comm] using increasing_mem_dPositive n i j h
    · right; simpa [Pi.single_neg, add_comm] using sum_mem_dPositive n i j hij

theorem dcoroot_eq_functional {n : ℕ} (a : DRoot n) : coroot a = functional a.1 := by
  have hn : dot a.1 a.1 = 2 := by rcases a.2 with ⟨h, _⟩ | h; cases h; exact h
  ext x; simp [corootScale, hn]

theorem functional_dPositive_mem (n : ℕ) (x : Lattice (n + 2)) (hx : x ∈ dPositive n) :
    functional x ∈ AddSubmonoid.closure (Set.range (fun i => coroot (simpleD n i))) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact AddSubmonoid.subset_closure ⟨i, simpleD_coroot n i⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa using AddSubmonoid.add_mem _ ihx ihy

noncomputable def simpleSupportD (n : ℕ) : Finset (DRoot (n + 2)) := Finset.univ.image (simpleD n)

theorem simpleSupportD_set (n : ℕ) :
    (simpleSupportD n : Set (DRoot (n + 2))) = Set.range (simpleD n) := by
  simp [simpleSupportD]

/-- The actual D simple-root base, including simultaneous coroot positivity. -/
noncomputable def baseD (n : ℕ) : (pairingD (n + 2)).Base where
  support := simpleSupportD n
  linearIndepOn_root := by
    change LinearIndepOn ℤ (fun a : DRoot (n + 2) => a.1) (simpleSupportD n : Set (DRoot (n + 2)))
    rw [simpleSupportD_set]
    exact (linearIndepOn_range_iff (simpleD_injective n) (fun a : DRoot (n + 2) => a.1)).2 (simpleD_independent n)
  linearIndepOn_coroot := by
    change LinearIndepOn ℤ coroot (simpleSupportD n : Set (DRoot (n + 2)))
    rw [simpleSupportD_set]
    exact (linearIndepOn_range_iff (simpleD_injective n) coroot).2 (simpleD_coroot_independent n)
  root_mem_or_neg_mem a := by
    change a.1 ∈ AddSubmonoid.closure ((fun a : DRoot (n + 2) => a.1) '' (simpleSupportD n : Set (DRoot (n + 2)))) ∨
      -a.1 ∈ AddSubmonoid.closure ((fun a : DRoot (n + 2) => a.1) '' (simpleSupportD n : Set (DRoot (n + 2))))
    rw [simpleSupportD_set, ← Set.range_comp]
    exact root_mem_dPositive n a
  coroot_mem_or_neg_mem a := by
    change coroot a ∈ AddSubmonoid.closure (coroot '' (simpleSupportD n : Set (DRoot (n + 2)))) ∨
      -coroot a ∈ AddSubmonoid.closure (coroot '' (simpleSupportD n : Set (DRoot (n + 2))))
    rw [simpleSupportD_set, ← Set.range_comp, dcoroot_eq_functional]
    rcases root_mem_dPositive n a with h | h
    · exact Or.inl (functional_dPositive_mem n _ h)
    · right; simpa only [functional_neg, Function.comp_def] using functional_dPositive_mem n _ h

noncomputable def baseDIndexEquiv (n : ℕ) : Fin (n + 2) ≃ (baseD n).support :=
  Equiv.ofBijective
    (fun i => ⟨simpleD n i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨by intro i j h; exact simpleD_injective n (congrArg Subtype.val h), by
      intro a
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.2
      exact ⟨i, Subtype.ext hi⟩⟩

theorem baseD_cartan (n : ℕ) (i j : Fin (n + 2)) :
    (baseD n).cartanMatrix (baseDIndexEquiv n i) (baseDIndexEquiv n j) =
      CartanMatrix.D (n + 2) i j := by
  change (pairingD (n + 2)).pairingIn ℤ (simpleD n i) (simpleD n j) = _
  have hp := (pairingD (n + 2)).algebraMap_pairingIn ℤ (simpleD n i) (simpleD n j)
  change (pairingD (n + 2)).pairingIn ℤ (simpleD n i) (simpleD n j) =
    coroot (simpleD n j) (simpleD n i).1 at hp
  exact hp.trans (simpleD_cartan n i j)

end Atlas.Chevalley.ClassicalData




