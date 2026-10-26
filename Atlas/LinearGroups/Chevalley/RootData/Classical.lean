import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma

/-! Integral coordinate root pairings of types B and D, with C the dual of B.
The roots are actual integer vectors of squared length one or two; D omits length one.
No root-system, group-order, or simplicity hypotheses are supplied by a caller.
Exact signed-support classification and simple bases remain subsequent obligations.
-/
namespace Atlas.Chevalley.ClassicalData

abbrev Lattice (n : ℕ) := Fin n → ℤ

def dot {n : ℕ} (x y : Lattice n) : ℤ := ∑ i, x i * y i

theorem dot_comm {n : ℕ} (x y : Lattice n) : dot x y = dot y x := by
  simp only [dot, mul_comm]

@[simp] theorem dot_add_left {n : ℕ} (x y z : Lattice n) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

@[simp] theorem dot_add_right {n : ℕ} (x y z : Lattice n) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

@[simp] theorem dot_sub_left {n : ℕ} (x y z : Lattice n) :
    dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

@[simp] theorem dot_sub_right {n : ℕ} (x y z : Lattice n) :
    dot x (y - z) = dot x y - dot x z := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem dot_smul_left {n : ℕ} (t : ℤ) (x y : Lattice n) :
    dot (t • x) y = t * dot x y := by
  simp [dot, Finset.mul_sum, mul_assoc]

@[simp] theorem dot_smul_right {n : ℕ} (t : ℤ) (x y : Lattice n) :
    dot x (t • y) = t * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm y x]

@[simp] theorem dot_single {n : ℕ} (x : Lattice n) (i : Fin n) (t : ℤ) :
    dot x (Pi.single i t) = x i * t := by
  simp [dot, Pi.single_apply, mul_ite]

/-- Coordinate vector as an integral functional; a concrete perfect-dual ambient lattice. -/
def functional {n : ℕ} (x : Lattice n) : Module.Dual ℤ (Lattice n) where
  toFun := dot x
  map_add' := dot_add_right x
  map_smul' t y := by
    change dot x (t • y) = t * dot x y
    exact dot_smul_right t x y

@[simp] theorem functional_apply {n : ℕ} (x y : Lattice n) : functional x y = dot x y := rfl

def Root (n : ℕ) (allowShort : Bool) :=
  {x : Lattice n // (allowShort = true ∧ dot x x = 1) ∨ dot x x = 2}

abbrev BRoot (n : ℕ) := Root n true
abbrev DRoot (n : ℕ) := Root n false

/-- The bounded-length condition is a concrete finite coordinate restriction. -/
theorem coordinate_bounds {n : ℕ} {b : Bool} (a : Root n b) (i : Fin n) :
    -1 ≤ a.1 i ∧ a.1 i ≤ 1 := by
  have hi : a.1 i * a.1 i ≤ dot a.1 a.1 :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (a.1 j)) (Finset.mem_univ i)
  have hn : dot a.1 a.1 ≤ 2 := by
    rcases a.2 with ⟨_, h⟩ | h <;> omega
  constructor
  · by_contra h
    have hlt : a.1 i ≤ -2 := by omega
    nlinarith
  · by_contra h
    have hgt : 2 ≤ a.1 i := by omega
    nlinarith

theorem coordinate_cases {n : ℕ} {b : Bool} (a : Root n b) (i : Fin n) :
    a.1 i = -1 ∨ a.1 i = 0 ∨ a.1 i = 1 := by
  have := coordinate_bounds a i
  omega

/-- Finiteness comes from coordinate bounds, not from an assumed root count. -/
instance rootFinite (n : ℕ) (b : Bool) : Finite (Root n b) := by
  let f : Root n b → (Fin n → Set.Icc (-1 : ℤ) 1) :=
    fun a i => ⟨a.1 i, coordinate_bounds a i⟩
  apply Finite.of_injective f
  intro a c h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

noncomputable instance rootFintype (n : ℕ) (b : Bool) : Fintype (Root n b) :=
  Fintype.ofFinite _

/-- The coroot multiplier is two for short roots and one for long roots. -/
def corootScale {n : ℕ} {b : Bool} (a : Root n b) : ℤ :=
  if dot a.1 a.1 = 1 then 2 else 1

theorem scale_norm {n : ℕ} {b : Bool} (a : Root n b) :
    corootScale a * dot a.1 a.1 = 2 := by
  rcases a.2 with ⟨_, h⟩ | h <;> simp [corootScale, h]

theorem scale_ne_zero {n : ℕ} {b : Bool} (a : Root n b) : corootScale a ≠ 0 := by
  simp only [corootScale]; split_ifs <;> norm_num

/-- The actual integral root reflection, simultaneously valid for B and D. -/
def reflect {n : ℕ} {b : Bool} (a : Root n b) (x : Lattice n) : Lattice n :=
  x - (corootScale a * dot a.1 x) • a.1

theorem reflect_dot {n : ℕ} {b : Bool} (a : Root n b) (x : Lattice n) :
    dot a.1 (reflect a x) = -dot a.1 x := by
  simp only [reflect, dot_sub_right, dot_smul_right]
  calc
    dot a.1 x - corootScale a * dot a.1 x * dot a.1 a.1 =
        dot a.1 x - dot a.1 x * (corootScale a * dot a.1 a.1) := by ring
    _ = -dot a.1 x := by rw [scale_norm]; ring

theorem reflect_involutive {n : ℕ} {b : Bool} (a : Root n b) :
    Function.Involutive (reflect a) := by
  intro x
  unfold reflect at ⊢
  rw [show dot a.1 (x - (corootScale a * dot a.1 x) • a.1) = -dot a.1 x from reflect_dot a x]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem reflect_norm {n : ℕ} {b : Bool} (a : Root n b) (x : Lattice n) :
    dot (reflect a x) (reflect a x) = dot x x := by
  simp only [reflect, dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right]
  rw [dot_comm x a.1]
  linear_combination (corootScale a * dot a.1 x ^ 2) * scale_norm a

/-- Reflection acts on the actual set of bounded-length integer vectors. -/
def reflectionPerm {n : ℕ} {b : Bool} (a : Root n b) : Equiv.Perm (Root n b) where
  toFun x := ⟨reflect a x.1, by simpa only [reflect_norm] using x.2⟩
  invFun x := ⟨reflect a x.1, by simpa only [reflect_norm] using x.2⟩
  left_inv x := by apply Subtype.ext; exact reflect_involutive a x.1
  right_inv x := by apply Subtype.ext; exact reflect_involutive a x.1

@[simp] theorem reflectionPerm_scale {n : ℕ} {b : Bool} (a x : Root n b) :
    corootScale (reflectionPerm a x) = corootScale x := by
  change (if dot (reflect a x.1) (reflect a x.1) = 1 then 2 else 1) = corootScale x
  rw [reflect_norm]
  rfl

def coroot {n : ℕ} {b : Bool} (a : Root n b) : Module.Dual ℤ (Lattice n) :=
  corootScale a • functional a.1

@[simp] theorem coroot_apply {n : ℕ} {b : Bool} (a : Root n b) (x : Lattice n) :
    coroot a x = corootScale a * dot a.1 x := rfl

/-- Distinct roots have distinct coroot functionals, including the two root lengths. -/
theorem coroot_injective {n : ℕ} {b : Bool} : Function.Injective (@coroot n b) := by
  intro a c h
  have hv : corootScale a • a.1 = corootScale c • c.1 := by
    funext i
    have he := congrArg (fun f : Module.Dual ℤ (Lattice n) => f (Pi.single i 1)) h
    simpa only [coroot_apply, dot_single, mul_one, Pi.smul_apply, smul_eq_mul] using he
  have hn := congrArg (fun x : Lattice n => dot x x) hv
  simp only [dot_smul_left, dot_smul_right] at hn
  have hs : corootScale a = corootScale c := by
    rcases a.2 with ⟨_, ha⟩ | ha <;> rcases c.2 with ⟨_, hc⟩ | hc <;>
      simp [corootScale, ha, hc] at hn ⊢
  apply Subtype.ext
  funext i
  have hi := congrFun hv i
  simp only [Pi.smul_apply, smul_eq_mul, hs] at hi
  exact mul_left_cancel₀ (scale_ne_zero c) hi

theorem reflection_coroot {n : ℕ} {b : Bool} (a c : Root n b) :
    coroot c - coroot c a.1 • coroot a = coroot (reflectionPerm a c) := by
  apply LinearMap.ext
  intro x
  change corootScale c * dot c.1 x -
    (corootScale c * dot c.1 a.1) * (corootScale a * dot a.1 x) =
    corootScale (reflectionPerm a c) * dot (reflect a c.1) x
  rw [reflectionPerm_scale, reflect, dot_sub_left, dot_smul_left, dot_comm c.1 a.1]
  ring

/-- Concrete integral pairing: B for allowShort=true, D for allowShort=false. -/
def pairing (n : ℕ) (allowShort : Bool) :
    RootPairing (Root n allowShort) ℤ (Lattice n) (Module.Dual ℤ (Lattice n)) where
  toLinearMap := Module.Dual.eval ℤ (Lattice n)
  root := ⟨Subtype.val, Subtype.val_injective⟩
  coroot := ⟨coroot, coroot_injective⟩
  root_coroot_two a := scale_norm a
  reflectionPerm := reflectionPerm
  reflectionPerm_root a c := rfl
  reflectionPerm_coroot := reflection_coroot

/-- B in Z^n paired with its ordinary coordinate dual. -/
def pairingB (n : ℕ) := pairing n true

/-- D in Z^n paired with its ordinary coordinate dual. -/
def pairingD (n : ℕ) := pairing n false

/-- C is the dual integral pairing; its roots are 2e_i and e_i±e_j. -/
def pairingC (n : ℕ) := (pairingB n).flip

/-- Signed coordinate vectors are actual short B roots. -/
def shortRoot {n : ℕ} (i : Fin n) (s : ℤ) (hs : s = 1 ∨ s = -1) : BRoot n :=
  ⟨Pi.single i s, Or.inl ⟨rfl, by rcases hs with rfl | rfl <;> simp [dot, Pi.single_apply]⟩⟩

/-- Every signed pair of distinct coordinate vectors is a long B or D root. -/
def longRoot {n : ℕ} (allowShort : Bool) (i j : Fin n) (hij : i ≠ j)
    (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) : Root n allowShort :=
  ⟨Pi.single i s + Pi.single j t, Or.inr (by
    simp only [dot_add_left, dot_add_right, dot_single]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [Pi.single_apply, hij, Ne.symm hij])⟩

@[simp] theorem short_scale {n : ℕ} (i : Fin n) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    corootScale (shortRoot i s hs) = 2 := by
  have hn : dot (shortRoot i s hs).1 (shortRoot i s hs).1 = 1 := by
    rcases hs with rfl | rfl <;> simp [shortRoot, dot, Pi.single_apply]
  simp [corootScale, hn]

@[simp] theorem long_scale {n : ℕ} (allowShort : Bool) (i j : Fin n) (hij : i ≠ j)
    (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    corootScale (longRoot allowShort i j hij s t hs ht) = 1 := by
  have hn : dot (longRoot allowShort i j hij s t hs ht).1
      (longRoot allowShort i j hij s t hs ht).1 = 2 := by
    simp only [longRoot, dot_add_left, dot_add_right, dot_single]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      simp [Pi.single_apply, hij, Ne.symm hij]
  simp [corootScale, hn]

/-- Reflection in a coordinate root negates exactly that coordinate. -/
theorem reflect_short {n : ℕ} (i : Fin n) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (x : Lattice n) (k : Fin n) :
    reflect (shortRoot i s hs) x k = if k = i then -x k else x k := by
  rw [reflect, short_scale]
  simp only [shortRoot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [dot_comm, dot_single]
  rcases hs with rfl | rfl <;> by_cases hk : k = i <;> simp [Pi.single_apply, hk] <;> ring

/-- The short B coroot is the long C root 2s e_i in dual coordinates. -/
theorem coroot_short {n : ℕ} (i : Fin n) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (x : Lattice n) : coroot (shortRoot i s hs) x = 2 * s * x i := by
  rw [coroot_apply, short_scale]
  change 2 * dot (Pi.single i s) x = _
  rw [dot_comm, dot_single]
  ring

/-- A long B/D coroot is the same signed pair of coordinate functionals. -/
theorem coroot_long {n : ℕ} (allowShort : Bool) (i j : Fin n) (hij : i ≠ j)
    (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (x : Lattice n) :
    coroot (longRoot allowShort i j hij s t hs ht) x = s * x i + t * x j := by
  rw [coroot_apply, long_scale]
  change 1 * dot (Pi.single i s + Pi.single j t) x = _
  rw [one_mul, dot_add_left, dot_comm (Pi.single i s), dot_comm (Pi.single j t), dot_single, dot_single]
  ring

/-- The exact nonzero coordinate support of a concrete root. -/
def support {n : ℕ} {b : Bool} (a : Root n b) : Finset (Fin n) :=
  Finset.univ.filter fun i => a.1 i ≠ 0

@[simp] theorem mem_support {n : ℕ} {b : Bool} (a : Root n b) (i : Fin n) :
    i ∈ support a ↔ a.1 i ≠ 0 := by simp [support]

/-- Since every coordinate is 0 or ±1, squared length equals support cardinality. -/
theorem norm_eq_card_support {n : ℕ} {b : Bool} (a : Root n b) :
    dot a.1 a.1 = (support a).card := by
  calc
    dot a.1 a.1 = ∑ i : Fin n, if a.1 i ≠ 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases coordinate_cases a i with h | h | h <;> simp [h]
    _ = (support a).card := by simp [support, Finset.sum_ite]

theorem support_card_cases {n : ℕ} {b : Bool} (a : Root n b) :
    (b = true ∧ (support a).card = 1) ∨ (support a).card = 2 := by
  have h := a.2
  rw [norm_eq_card_support] at h
  rcases h with ⟨hb, h⟩ | h
  · exact Or.inl ⟨hb, by exact_mod_cast h⟩
  · exact Or.inr (by exact_mod_cast h)

theorem sign_of_mem_support {n : ℕ} {b : Bool} (a : Root n b) {i : Fin n}
    (hi : i ∈ support a) : a.1 i = 1 ∨ a.1 i = -1 := by
  have hn := (mem_support a i).1 hi
  rcases coordinate_cases a i with h | h | h
  · exact Or.inr h
  · exact False.elim (hn h)
  · exact Or.inl h

theorem coordinates_of_singleton_support {n : ℕ} {b : Bool} (a : Root n b)
    (i : Fin n) (hi : support a = {i}) : a.1 = Pi.single i (a.1 i) := by
  funext k
  by_cases hk : k = i
  · subst k; simp
  · have hz : a.1 k = 0 := by
      by_contra hn
      have hm := (mem_support a k).2 hn
      rw [hi] at hm
      simpa [hk] using hm
    simp [Pi.single_apply, hk, hz]

theorem coordinates_of_pair_support {n : ℕ} {b : Bool} (a : Root n b)
    (i j : Fin n) (hij : i ≠ j) (h : support a = {i, j}) :
    a.1 = Pi.single i (a.1 i) + Pi.single j (a.1 j) := by
  funext k
  by_cases hi : k = i
  · subst k; simp [Ne.symm hij]
  by_cases hj : k = j
  · subst k; simp [hij]
  · have hz : a.1 k = 0 := by
      by_contra hn
      have hm := (mem_support a k).2 hn
      rw [h] at hm
      simpa [hi, hj] using hm
    simp [Pi.single_apply, hi, hj, hz]

/-- Exact signed-coordinate classification, not only membership examples. -/
theorem signed_support_classification {n : ℕ} {b : Bool} (a : Root n b) :
    (b = true ∧ ∃ i : Fin n, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ a.1 = Pi.single i s) ∨
    ∃ i j : Fin n, i ≠ j ∧ ∃ s t : ℤ,
      (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
      a.1 = Pi.single i s + Pi.single j t := by
  rcases support_card_cases a with ⟨hb, h⟩ | h
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    left
    refine ⟨hb, i, a.1 i, ?_, coordinates_of_singleton_support a i hi⟩
    apply sign_of_mem_support a
    simp [hi]
  · obtain ⟨i, j, hij, h⟩ := Finset.card_eq_two.mp h
    right
    refine ⟨i, j, hij, a.1 i, a.1 j, ?_, ?_, coordinates_of_pair_support a i j hij h⟩
    · apply sign_of_mem_support a; simp [h]
    · apply sign_of_mem_support a; simp [h]

/-- Every root has a coordinate equal to ±1, enabling primitive-vector arguments. -/
theorem exists_signed_coordinate {n : ℕ} {b : Bool} (a : Root n b) :
    ∃ i : Fin n, a.1 i = 1 ∨ a.1 i = -1 := by
  have hp : 0 < (support a).card := by
    rcases support_card_cases a with ⟨_, h⟩ | h <;> omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
  exact ⟨i, sign_of_mem_support a hi⟩

/-- The actual B/D integral root pairings are reduced in every dimension. -/
instance reduced (n : ℕ) (b : Bool) : (pairing n b).IsReduced where
  eq_or_eq_neg a c h := by
    have he := (pairing n b).pairing_smul_root_eq_of_not_linearIndependent h
    change coroot a c.1 • a.1 = (2 : ℤ) • c.1 at he
    obtain ⟨i, hi⟩ := exists_signed_coordinate a
    have hc := congrFun he i
    simp only [Pi.smul_apply, smul_eq_mul] at hc
    have hj := coordinate_cases c i
    have hcoef : coroot a c.1 = -2 ∨ coroot a c.1 = 0 ∨ coroot a c.1 = 2 := by
      rcases hi with hi | hi <;> rcases hj with hj | hj | hj <;> rw [hi, hj] at hc <;> omega
    rcases hcoef with hm | hz | hp
    · right
      change a.1 = -c.1
      funext k
      have hk := congrFun he k
      simp only [Pi.smul_apply, smul_eq_mul, hm, Pi.neg_apply] at hk ⊢
      omega
    · obtain ⟨k, hk⟩ := exists_signed_coordinate c
      have heₖ := congrFun he k
      simp only [Pi.smul_apply, smul_eq_mul, hz, zero_mul] at heₖ
      rcases hk with hk | hk <;> omega
    · left
      change a.1 = c.1
      funext k
      have hk := congrFun he k
      simp only [Pi.smul_apply, smul_eq_mul, hp] at hk
      omega

instance reducedB (n : ℕ) : (pairingB n).IsReduced := reduced n true
instance reducedD (n : ℕ) : (pairingD n).IsReduced := reduced n false
instance reducedC (n : ℕ) : (pairingC n).IsReduced := by
  change (pairingB n).flip.IsReduced
  infer_instance

/-- A sign assignment on an exact coordinate support. -/
def signedVector {n : ℕ} (s : Finset (Fin n)) (f : s → Bool) : Lattice n :=
  fun i => if h : i ∈ s then (if f ⟨i, h⟩ then 1 else -1) else 0

theorem signedVector_norm {n : ℕ} (s : Finset (Fin n)) (f : s → Bool) :
    dot (signedVector s f) (signedVector s f) = s.card := by
  calc
    dot (signedVector s f) (signedVector s f) =
        ∑ i : Fin n, if i ∈ s then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i ∈ s
      · cases hf : f ⟨i, h⟩ <;> simp [signedVector, h, hf]
      · simp [signedVector, h]
    _ = s.card := by simp

abbrev LongCode (n : ℕ) := (s : {s : Finset (Fin n) // s.card = 2}) × (s.1 → Bool)

/-- Every two-coordinate sign assignment is a D root. -/
def decodeLong {n : ℕ} (c : LongCode n) : DRoot n :=
  ⟨signedVector c.1.1 c.2, Or.inr (by rw [signedVector_norm, c.1.2]; rfl)⟩

theorem support_decodeLong {n : ℕ} (c : LongCode n) : support (decodeLong c) = c.1.1 := by
  ext i
  simp only [mem_support]
  change signedVector c.1.1 c.2 i ≠ 0 ↔ i ∈ c.1.1
  by_cases hi : i ∈ c.1.1
  · cases hf : c.2 ⟨i, hi⟩ <;> simp [signedVector, hi, hf]
  · simp [signedVector, hi]

def encodeLong {n : ℕ} (a : DRoot n) : LongCode n :=
  ⟨⟨support a, by rcases support_card_cases a with ⟨h, _⟩ | h; cases h; exact h⟩,
    fun i => decide (a.1 i.1 = 1)⟩

theorem decode_encodeLong {n : ℕ} (a : DRoot n) : decodeLong (encodeLong a) = a := by
  apply Subtype.ext
  funext i
  change signedVector (support a) (fun i => decide (a.1 i.1 = 1)) i = a.1 i
  by_cases hi : i ∈ support a
  · have hs := sign_of_mem_support a hi
    rcases hs with hs | hs <;> simp [signedVector, hi, hs]
  · have hz : a.1 i = 0 := by simpa only [mem_support, not_not] using hi
    simp [signedVector, hi, hz]

theorem decodeLong_injective {n : ℕ} : Function.Injective (@decodeLong n) := by
  rintro ⟨s, f⟩ ⟨t, g⟩ h
  have hs : s = t := by
    apply Subtype.ext
    exact (support_decodeLong ⟨s, f⟩).symm.trans
      ((congrArg support h).trans (support_decodeLong ⟨t, g⟩))
  cases hs
  have fg : f = g := by
    funext i
    have hi := congrArg (fun a : DRoot n => a.1 i.1) h
    change signedVector s.1 f i.1 = signedVector s.1 g i.1 at hi
    cases hf : f i <;> cases hg : g i <;> simp [signedVector, i.2, hf, hg] at hi ⊢
  exact congrArg (fun f => Sigma.mk s f) fg

theorem encode_decodeLong {n : ℕ} (c : LongCode n) : encodeLong (decodeLong c) = c := by
  apply decodeLong_injective
  exact decode_encodeLong (decodeLong c)

/-- A bijective support/sign encoding establishes the root count without enumeration. -/
def longCodeEquiv (n : ℕ) : DRoot n ≃ LongCode n where
  toFun := encodeLong
  invFun := decodeLong
  left_inv := decode_encodeLong
  right_inv := encode_decodeLong

/-- Four choices of signs for each unordered pair of coordinates. -/
theorem card_droot_choose (n : ℕ) : Fintype.card (DRoot n) = 4 * n.choose 2 := by
  rw [Fintype.card_congr (longCodeEquiv n), Fintype.card_sigma]
  have hc : ∀ s : {s : Finset (Fin n) // s.card = 2}, Fintype.card (s.1 → Bool) = 4 := by
    intro s
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, s.2]
    rfl
  simp only [hc]
  simp [Fintype.card_finset_len, Nat.mul_comm]

def decodeShort {n : ℕ} (c : Fin n × Bool) : BRoot n :=
  shortRoot c.1 (if c.2 then 1 else -1) (by cases c.2 <;> simp)

theorem decodeShort_norm {n : ℕ} (c : Fin n × Bool) :
    dot (decodeShort c).1 (decodeShort c).1 = 1 := by
  cases hc : c.2 <;> simp [decodeShort, shortRoot, dot, Pi.single_apply, hc]

theorem decodeShort_injective {n : ℕ} : Function.Injective (@decodeShort n) := by
  intro p q h
  have hi : p.1 = q.1 := by
    by_contra hn
    have he := congrArg (fun a : BRoot n => a.1 p.1) h
    cases hp : p.2 <;> simp [decodeShort, shortRoot, hp, Pi.single_apply, hn, Ne.symm hn] at he
  have he := congrArg (fun a : BRoot n => a.1 p.1) h
  have hb : p.2 = q.2 := by
    cases hp : p.2 <;> cases hq : q.2 <;>
      simp [decodeShort, shortRoot, hi, hp, hq] at he ⊢
  exact Prod.ext hi hb

def decodeB {n : ℕ} : (Fin n × Bool) ⊕ DRoot n → BRoot n
  | .inl c => decodeShort c
  | .inr a => ⟨a.1, Or.inr (by rcases a.2 with ⟨h, _⟩ | h; cases h; exact h)⟩

theorem decodeB_injective {n : ℕ} : Function.Injective (@decodeB n) := by
  intro p q h
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (decodeShort_injective h)
    | inr q =>
      have hn := congrArg (fun a : BRoot n => dot a.1 a.1) h
      change dot (decodeShort p).1 (decodeShort p).1 = dot q.1 q.1 at hn
      rw [decodeShort_norm] at hn
      rcases q.2 with ⟨hq, _⟩ | hq
      · cases hq
      · omega
  | inr p =>
    cases q with
    | inl q =>
      have hn := congrArg (fun a : BRoot n => dot a.1 a.1) h
      change dot p.1 p.1 = dot (decodeShort q).1 (decodeShort q).1 at hn
      rw [decodeShort_norm] at hn
      rcases p.2 with ⟨hp, _⟩ | hp
      · cases hp
      · omega
    | inr q => exact congrArg Sum.inr (Subtype.ext (congrArg (fun a : BRoot n => a.1) h))

theorem decodeB_surjective {n : ℕ} : Function.Surjective (@decodeB n) := by
  intro a
  rcases a.2 with ⟨_, hn⟩ | hn
  · have hc : (support a).card = 1 := by rw [norm_eq_card_support] at hn; exact_mod_cast hn
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    have hs := sign_of_mem_support a (i := i) (by simp [hi])
    have hv := coordinates_of_singleton_support a i hi
    rcases hs with hs | hs
    · refine ⟨Sum.inl (i, true), ?_⟩
      apply Subtype.ext
      simpa [decodeB, decodeShort, shortRoot, hs] using hv.symm
    · refine ⟨Sum.inl (i, false), ?_⟩
      apply Subtype.ext
      simpa [decodeB, decodeShort, shortRoot, hs] using hv.symm
  · exact ⟨Sum.inr ⟨a.1, Or.inr hn⟩, Subtype.ext rfl⟩

noncomputable def bCodeEquiv (n : ℕ) : ((Fin n × Bool) ⊕ DRoot n) ≃ BRoot n :=
  Equiv.ofBijective decodeB ⟨decodeB_injective, decodeB_surjective⟩

/-- Two signed axes per coordinate plus four sign assignments per coordinate pair. -/
theorem card_broot_choose (n : ℕ) :
    Fintype.card (BRoot n) = 2 * n + 4 * n.choose 2 := by
  rw [← Fintype.card_congr (bCodeEquiv n), Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, card_droot_choose]
  omega

/-- The uniform D root count in its conventional polynomial form. -/
theorem card_droot (n : ℕ) : Fintype.card (DRoot n) = 2 * n * (n - 1) := by
  rw [card_droot_choose]
  cases n with
  | zero => simp
  | succ n =>
    have h := Nat.add_one_mul_choose_eq n 1
    simp only [Nat.choose_one_right] at h
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    nlinarith

/-- The common B/C root count in its conventional polynomial form. -/
theorem card_broot (n : ℕ) : Fintype.card (BRoot n) = 2 * n ^ 2 := by
  rw [card_broot_choose]
  cases n with
  | zero => simp
  | succ n =>
    have h := Nat.add_one_mul_choose_eq n 1
    simp only [Nat.choose_one_right] at h
    nlinarith

end Atlas.Chevalley.ClassicalData





