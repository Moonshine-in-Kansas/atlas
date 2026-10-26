import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Cartan

/-! # Integral type-A root pairing

The roots in the ambient integral coordinate lattice are the differences of distinct
coordinate vectors. This is the GL ambient root datum; the root-span/base and the
simply connected weight lattice are separate subsequent obligations.
-/

namespace Atlas.Chevalley.TypeAData

/-- Ordered distinct coordinate indices. Type A of rank r uses n = r + 1. -/
abbrev Root (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

abbrev Lattice (n : ℕ) := Fin n → ℤ

/-- The integral root e_i - e_j. -/
def root {n : ℕ} (a : Root n) : Lattice n :=
  Pi.single a.1.1 1 - Pi.single a.1.2 1

/-- The corresponding coroot functional x ↦ x_i - x_j. -/
def coroot {n : ℕ} (a : Root n) : Module.Dual ℤ (Lattice n) where
  toFun x := x a.1.1 - x a.1.2
  map_add' x y := by simp only [Pi.add_apply]; abel
  map_smul' t x := by simp [mul_sub]

@[simp] theorem coroot_apply {n : ℕ} (a : Root n) (x : Lattice n) :
    coroot a x = x a.1.1 - x a.1.2 := rfl

@[simp] theorem root_first {n : ℕ} (a : Root n) : root a a.1.1 = 1 := by
  simp [root, a.2]

@[simp] theorem root_second {n : ℕ} (a : Root n) : root a a.1.2 = -1 := by
  simp [root, Ne.symm a.2]

theorem root_injective {n : ℕ} : Function.Injective (@root n) := by
  intro a b hab
  have h₁ : a.1.1 = b.1.1 := by
    have h := congrFun hab a.1.1
    rw [root_first] at h
    by_contra hn
    by_cases hn₂ : b.1.2 = a.1.1 <;>
      simp [root, hn, hn₂] at h
  have h₂ : a.1.2 = b.1.2 := by
    have h := congrFun hab a.1.2
    rw [root_second] at h
    by_contra hn
    have hne : b.1.1 ≠ a.1.2 := by rw [← h₁]; exact a.2
    simp [root, hn, hne] at h
  exact Subtype.ext (Prod.ext h₁ h₂)

/-- Coordinate permutations act on the actual root index set. -/
def permute {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Root n) where
  toFun a := ⟨(e a.1.1, e a.1.2), fun h => a.2 (e.injective h)⟩
  invFun a := ⟨(e.symm a.1.1, e.symm a.1.2), fun h => a.2 (e.symm.injective h)⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp

/-- Reflection in e_i-e_j permutes the two corresponding coordinates. -/
def reflectionPerm {n : ℕ} (a : Root n) : Equiv.Perm (Root n) :=
  permute (Equiv.swap a.1.1 a.1.2)

@[simp] theorem root_coroot_two {n : ℕ} (a : Root n) : coroot a (root a) = 2 := by
  simp

theorem coroot_on_single {n : ℕ} (a : Root n) (k : Fin n) :
    coroot a (Pi.single k 1) = root a k := by
  simp [root, Pi.single_apply, eq_comm]

theorem coroot_injective {n : ℕ} : Function.Injective (@coroot n) := by
  intro a b hab
  apply root_injective
  funext k
  simpa only [coroot_on_single] using congrArg (fun f => f (Pi.single k 1)) hab

theorem root_permute {n : ℕ} (e : Equiv.Perm (Fin n)) (a : Root n) (k : Fin n) :
    root (permute e a) (e k) = root a k := by
  simp [root, permute, Pi.single_apply]

theorem reflection_coordinate {n : ℕ} (a : Root n) (x : Lattice n) (k : Fin n) :
    x k - coroot a x * root a k = x (Equiv.swap a.1.1 a.1.2 k) := by
  by_cases h₁ : k = a.1.1
  · subst k; simp
  by_cases h₂ : k = a.1.2
  · subst k; simp
  · simp [root, h₁, h₂,
      Equiv.swap_apply_of_ne_of_ne h₁ h₂]

theorem reflection_root {n : ℕ} (a b : Root n) :
    root b - coroot a (root b) • root a = root (reflectionPerm a b) := by
  funext k
  change root b k - coroot a (root b) * root a k = root (reflectionPerm a b) k
  rw [reflection_coordinate]
  have h := root_permute (Equiv.swap a.1.1 a.1.2) b
    (Equiv.swap a.1.1 a.1.2 k)
  simpa only [Equiv.swap_apply_self, reflectionPerm] using h.symm

theorem reflection_coroot {n : ℕ} (a b : Root n) :
    coroot b - coroot b (root a) • coroot a = coroot (reflectionPerm a b) := by
  apply LinearMap.ext
  intro x
  change coroot b x - coroot b (root a) * coroot a x =
    x (Equiv.swap a.1.1 a.1.2 b.1.1) - x (Equiv.swap a.1.1 a.1.2 b.1.2)
  rw [← reflection_coordinate a x b.1.1, ← reflection_coordinate a x b.1.2]
  simp only [coroot_apply]
  ring

/-- An actual integral root pairing, including perfect pairing and both reflection axioms. -/
def pairing (n : ℕ) : RootPairing (Root n) ℤ (Lattice n) (Module.Dual ℤ (Lattice n)) where
  toLinearMap := Module.Dual.eval ℤ (Lattice n)
  root := ⟨root, root_injective⟩
  coroot := ⟨coroot, coroot_injective⟩
  root_coroot_two := root_coroot_two
  reflectionPerm := reflectionPerm
  reflectionPerm_root := reflection_root
  reflectionPerm_coroot := reflection_coroot

theorem root_coordinate_cases {n : ℕ} (a : Root n) (k : Fin n) :
    root a k = -1 ∨ root a k = 0 ∨ root a k = 1 := by
  by_cases h₁ : k = a.1.1
  · subst k; simp
  by_cases h₂ : k = a.1.2
  · subst k; simp
  · simp [root, h₁, h₂]

/-- The integral root pairing is reduced, uniformly in the number of coordinates. -/
instance reduced (n : ℕ) : (pairing n).IsReduced where
  eq_or_eq_neg a b h := by
    have he := (pairing n).pairing_smul_root_eq_of_not_linearIndependent h
    change coroot a (root b) • root a = (2 : ℤ) • root b at he
    have hc := congrFun he a.1.1
    simp only [Pi.smul_apply, smul_eq_mul, root_first, mul_one] at hc
    rcases root_coordinate_cases b a.1.1 with hm | hz | hp
    · right
      change root a = -root b
      have hc₂ : coroot a (root b) = -2 := by omega
      funext k
      have hk := congrFun he k
      simp only [Pi.smul_apply, smul_eq_mul, hc₂, Pi.neg_apply] at hk ⊢
      omega
    · have hc₂ : coroot a (root b) = 0 := by omega
      have hk := congrFun he b.1.1
      simp [hc₂] at hk
    · left
      change root a = root b
      have hc₂ : coroot a (root b) = 2 := by omega
      funext k
      have hk := congrFun he k
      simp only [Pi.smul_apply, smul_eq_mul, hc₂] at hk
      omega

/-- The actual number of roots; no group-order formula is used. -/
theorem card_root (n : ℕ) : Fintype.card (Root n) = n * (n - 1) := by
  calc
    Fintype.card (Root n) = ((Finset.univ : Finset (Fin n)).offDiag).card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (by intro p; simp)
    _ = n * (n - 1) := by simp [Nat.mul_sub]

/-- Consecutive coordinate differences, with the pinned A-r node numbering. -/
def simpleRoot {r : ℕ} (i : Fin r) : Root (r + 1) :=
  ⟨(i.castSucc, i.succ), by intro h; have := congrArg Fin.val h; simp at this⟩

/-- The actual coordinate pairing has exactly the specified type-A Cartan matrix. -/
theorem simple_cartan {r : ℕ} (i j : Fin r) :
    coroot (simpleRoot j) (root (simpleRoot i)) = CartanMatrix.A r i j := by
  simp only [coroot_apply, root, simpleRoot, Pi.sub_apply, Pi.single_apply,
    CartanMatrix.A, Matrix.of_apply, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- Cumulative coordinates recover coefficients in consecutive simple roots. -/
def prefixMap (r : ℕ) : Lattice (r + 1) →ₗ[ℤ] (Fin r → ℤ) where
  toFun x i := ∑ k ∈ Finset.univ.filter (fun k : Fin (r + 1) => k.val ≤ i.val), x k
  map_add' x y := by ext i; simp [Finset.sum_add_distrib]
  map_smul' t x := by ext i; simp [Finset.mul_sum]

theorem prefix_simple {r : ℕ} (j : Fin r) :
    prefixMap r (root (simpleRoot j)) = Pi.single j 1 := by
  funext i
  simp [prefixMap, root, simpleRoot, Finset.sum_sub_distrib,
    Pi.single_apply]
  simp only [Fin.ext_iff]
  split_ifs <;> omega

theorem simpleRoot_injective {r : ℕ} : Function.Injective (@simpleRoot r) := by
  intro i j h
  have hv := congrArg (fun a : Root (r + 1) => a.1.1.val) h
  exact Fin.ext hv

theorem simple_linearIndependent (r : ℕ) :
    LinearIndependent ℤ (fun i : Fin r => root (simpleRoot i)) := by
  apply LinearIndependent.of_comp (prefixMap r)
  have he : prefixMap r ∘ (fun i : Fin r => root (simpleRoot i)) = Pi.basisFun ℤ (Fin r) := by
    funext i
    simp [prefix_simple]
  rw [he]
  exact (Pi.basisFun ℤ (Fin r)).linearIndependent

/-- Every increasing coordinate difference is a nonnegative sum of simple roots. -/
theorem increasing_difference_mem {r : ℕ} (a b : Fin (r + 1)) (h : a ≤ b) :
    Pi.single a (1 : ℤ) - Pi.single b 1 ∈
      AddSubmonoid.closure (Set.range (fun i : Fin r => root (simpleRoot i))) := by
  revert h
  induction b using Fin.induction with
  | zero =>
    intro h
    have ha : a = 0 := by
      apply Fin.ext
      change a.val = 0
      change a.val ≤ 0 at h
      omega
    subst a
    simp
  | succ b ih =>
    intro h
    by_cases he : a = b.succ
    · subst a; simp
    have hle : a ≤ b.castSucc := by
      change a.val ≤ b.val
      have hv : a.val ≤ b.val + 1 := h
      have hne : a.val ≠ b.val + 1 := fun hh => he (Fin.ext hh)
      omega
    have hi := ih hle
    have hs : root (simpleRoot b) ∈
        AddSubmonoid.closure (Set.range (fun i : Fin r => root (simpleRoot i))) :=
      AddSubmonoid.subset_closure ⟨b, rfl⟩
    have ha := AddSubmonoid.add_mem _ hi hs
    simpa only [root, simpleRoot, sub_add_sub_cancel] using ha

/-- Evaluating a functional on coordinate vectors recovers its coefficient vector. -/
def dualCoordinates (n : ℕ) : Module.Dual ℤ (Lattice n) →ₗ[ℤ] Lattice n where
  toFun f k := f (Pi.single k 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem simple_coroot_linearIndependent (r : ℕ) :
    LinearIndependent ℤ (fun i : Fin r => coroot (simpleRoot i)) := by
  apply LinearIndependent.of_comp (dualCoordinates (r + 1))
  have he : dualCoordinates (r + 1) ∘ (fun i : Fin r => coroot (simpleRoot i)) =
      (fun i : Fin r => root (simpleRoot i)) := by
    funext i k
    exact coroot_on_single (simpleRoot i) k
  rw [he]
  exact simple_linearIndependent r

private theorem consecutive_difference_mem {M : Type*} [AddCommGroup M] {r : ℕ}
    (v : Fin (r + 1) → M) (a b : Fin (r + 1)) (h : a ≤ b) :
    v a - v b ∈ AddSubmonoid.closure
      (Set.range (fun i : Fin r => v i.castSucc - v i.succ)) := by
  revert h
  induction b using Fin.induction with
  | zero =>
    intro h
    have ha : a = 0 := by
      apply Fin.ext
      change a.val = 0
      change a.val ≤ 0 at h
      omega
    subst a
    simp
  | succ b ih =>
    intro h
    by_cases he : a = b.succ
    · subst a; simp
    have hle : a ≤ b.castSucc := by
      change a.val ≤ b.val
      have hv : a.val ≤ b.val + 1 := h
      have hne : a.val ≠ b.val + 1 := fun hh => he (Fin.ext hh)
      omega
    have hi := ih hle
    have hs : v b.castSucc - v b.succ ∈ AddSubmonoid.closure
        (Set.range (fun i : Fin r => v i.castSucc - v i.succ)) :=
      AddSubmonoid.subset_closure ⟨b, rfl⟩
    simpa only [sub_add_sub_cancel] using AddSubmonoid.add_mem _ hi hs

/-- A coordinate functional, used to telescope the coroots. -/
def coordinateProjection {n : ℕ} (k : Fin n) : Module.Dual ℤ (Lattice n) where
  toFun x := x k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coroot_eq_projection_sub {n : ℕ} (a : Root n) :
    coroot a = coordinateProjection a.1.1 - coordinateProjection a.1.2 := rfl

/-- The pinned consecutive-root support; no existential choice of base is involved. -/
def simpleSupport (r : ℕ) : Finset (Root (r + 1)) :=
  Finset.univ.image simpleRoot

theorem simpleSupport_set (r : ℕ) :
    (simpleSupport r : Set (Root (r + 1))) = Set.range simpleRoot := by
  simp [simpleSupport]

set_option maxHeartbeats 800000 in
/-- The specified type-A root pairing has the actual consecutive simple-root base. -/
def base (r : ℕ) : (pairing (r + 1)).Base where
  support := simpleSupport r
  linearIndepOn_root := by
    change LinearIndepOn ℤ root (simpleSupport r : Set (Root (r + 1)))
    rw [simpleSupport_set]
    exact (linearIndepOn_range_iff simpleRoot_injective root).2 (simple_linearIndependent r)
  linearIndepOn_coroot := by
    change LinearIndepOn ℤ coroot (simpleSupport r : Set (Root (r + 1)))
    rw [simpleSupport_set]
    exact (linearIndepOn_range_iff simpleRoot_injective coroot).2
      (simple_coroot_linearIndependent r)
  root_mem_or_neg_mem a := by
    change root a ∈ AddSubmonoid.closure (root '' (simpleSupport r : Set (Root (r + 1)))) ∨
      -root a ∈ AddSubmonoid.closure (root '' (simpleSupport r : Set (Root (r + 1))))
    rw [simpleSupport_set, ← Set.range_comp]
    simp only [Function.comp_def]
    rcases le_total a.1.1 a.1.2 with h | h
    · left
      exact increasing_difference_mem a.1.1 a.1.2 h
    · right
      simpa only [root, neg_sub] using increasing_difference_mem a.1.2 a.1.1 h
  coroot_mem_or_neg_mem a := by
    change coroot a ∈ AddSubmonoid.closure (coroot '' (simpleSupport r : Set (Root (r + 1)))) ∨
      -coroot a ∈ AddSubmonoid.closure (coroot '' (simpleSupport r : Set (Root (r + 1))))
    rw [simpleSupport_set, ← Set.range_comp]
    simp only [Function.comp_def]
    simp only [coroot_eq_projection_sub, simpleRoot]
    rcases le_total a.1.1 a.1.2 with h | h
    · left
      exact consecutive_difference_mem coordinateProjection a.1.1 a.1.2 h
    · right
      simpa only [neg_sub] using
        consecutive_difference_mem coordinateProjection a.1.2 a.1.1 h

/-- The chosen base is indexed by exactly the r consecutive coordinate differences. -/
noncomputable def baseIndexEquiv (r : ℕ) : Fin r ≃ (base r).support :=
  Equiv.ofBijective
    (fun i => ⟨simpleRoot i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨by
      intro i j h
      exact simpleRoot_injective (congrArg Subtype.val h), by
      intro a
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp] theorem baseIndexEquiv_apply (r : ℕ) (i : Fin r) :
    (baseIndexEquiv r i : Root (r + 1)) = simpleRoot i := rfl

/-- The genuine base has the pinned type-A Cartan matrix under its explicit numbering. -/
theorem base_cartan (r : ℕ) (i j : Fin r) :
    (base r).cartanMatrix (baseIndexEquiv r i) (baseIndexEquiv r j) =
      CartanMatrix.A r i j := by
  change (pairing (r + 1)).pairingIn ℤ (simpleRoot i) (simpleRoot j) = _
  have hp := (pairing (r + 1)).algebraMap_pairingIn ℤ (simpleRoot i) (simpleRoot j)
  change (pairing (r + 1)).pairingIn ℤ (simpleRoot i) (simpleRoot j) =
    coroot (simpleRoot j) (root (simpleRoot i)) at hp
  exact hp.trans (simple_cartan i j)

end Atlas.Chevalley.TypeAData
