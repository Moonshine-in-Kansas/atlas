import Atlas.LinearGroups.ReeF4.RootSuzukiActual
import Atlas.LinearGroups.ReeF4.RootGroupCommutator
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Elementary structure of the actual two-parameter root subgroup. Its binary
case is cyclic of order four; in the larger admissible fields its centre is
exactly the additive second-coordinate subgroup. This is not a statement of
order or simplicity for the ambient Ree group. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem parameter_mul (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b c d : F) :
    shortRootParameters m hcard (a,b) * shortRootParameters m hcard (c,d) =
      shortRootParameters m hcard (a+c,b+d+theta F m a*c) := by
  apply Subtype.ext
  exact shortRootPairEquiv_mul m hcard a b c d

private theorem parameter_zero (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    shortRootParameters m hcard (0,0) = 1 := by
  apply Subtype.ext
  exact shortRootPairEquiv_zero m hcard

theorem shortRootParameter_eq_one_iff (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    shortRootParameters m hcard (a,b) = 1 ↔ a = 0 ∧ b = 0 := by
  rw [← parameter_zero m hcard, (shortRootParameters m hcard).injective.eq_iff,
    Prod.mk.injEq]

theorem shortRootParameter_commute_iff (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b c d : F) :
    shortRootParameters m hcard (a,b) * shortRootParameters m hcard (c,d) =
      shortRootParameters m hcard (c,d) * shortRootParameters m hcard (a,b) ↔
    theta F m a*c = theta F m c*a := by
  rw [parameter_mul, parameter_mul, (shortRootParameters m hcard).injective.eq_iff]
  constructor
  · intro h
    have he := congrArg Prod.snd h
    change b+d+theta F m a*c = d+b+theta F m c*a at he
    rw [add_comm d b] at he
    exact add_left_cancel he
  · intro h
    apply Prod.ext
    · exact add_comm a c
    · change b+d+theta F m a*c = d+b+theta F m c*a
      rw [h]
      abel

theorem shortRootParameter_square (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    shortRootParameters m hcard (a,b)^2 =
      shortRootParameters m hcard (0,a*theta F m a) := by
  rw [pow_two, parameter_mul]
  simp only [CharTwo.add_self_eq_zero, zero_add, mul_comm (theta F m a) a]

theorem shortRootParameter_pow_four (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    shortRootParameters m hcard (a,b)^4 = 1 := by
  rw [show (4 : ℕ) = 2*2 by decide, pow_mul, shortRootParameter_square,
    shortRootParameter_square]
  simpa only [zero_mul] using parameter_zero m hcard

theorem shortRootSubgroup_pow_four (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (g : shortRootSubgroup m hcard) : g^4 = 1 := by
  obtain ⟨⟨a,b⟩, rfl⟩ := (shortRootParameters m hcard).surjective g
  exact shortRootParameter_pow_four m hcard a b

theorem shortRootParameter_order_four (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (ha : a ≠ 0) : orderOf (shortRootParameters m hcard (a,b)) = 4 := by
  have hs : shortRootParameters m hcard (a,b)^2 ≠ 1 := by
    rw [shortRootParameter_square]
    intro h
    have hz := (shortRootParameter_eq_one_iff m hcard 0 (a * theta F m a)).mp h
    exact (mul_ne_zero ha ((map_ne_zero (theta F m)).mpr ha)) hz.2
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hs
    (shortRootParameter_pow_four m hcard a b)

/-- The binary local root group, unlike the larger root groups, is cyclic. -/
theorem shortRootSubgroup_binary_cyclic (hcard : Nat.card F = 2^(2*0+1)) :
    IsCyclic (shortRootSubgroup 0 hcard) := by
  letI : Finite (shortRootSubgroup 0 hcard) :=
    Finite.of_equiv (F × F) (shortRootParameters 0 hcard)
  apply isCyclic_of_orderOf_eq_card (shortRootParameters 0 hcard (1,0))
  rw [shortRootParameter_order_four 0 hcard 1 0 one_ne_zero,
    card_shortRootSubgroup, hcard]
  norm_num

theorem shortRootSubgroup_binary_commutative (hcard : Nat.card F = 2^(2*0+1))
    (g h : shortRootSubgroup 0 hcard) : g*h = h*g := by
  obtain ⟨⟨a,b⟩, rfl⟩ := (shortRootParameters 0 hcard).surjective g
  obtain ⟨⟨c,d⟩, rfl⟩ := (shortRootParameters 0 hcard).surjective h
  apply (shortRootParameter_commute_iff 0 hcard a b c d).mpr
  have hc : Nat.card F = 2 := by simpa using hcard
  rw [Atlas.SuzukiFamily.theta_binary hc, Atlas.SuzukiFamily.theta_binary hc, mul_comm]

private theorem exists_theta_ne_self (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (hm : 1 ≤ m) : ∃ c : F, theta F m c ≠ c := by
  by_contra hn
  push_neg at hn
  have hz (x : F) : x = 0 ∨ x = 1 := by
    have hs := Atlas.SuzukiFamily.theta_square hcard x
    have he : x = x^2 := by simpa only [hn] using hs
    exact eq_zero_or_one_of_sq_eq_self he.symm
  have hs : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
    intro x
    rcases hz x with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, h.symm⟩
  have hc : Nat.card F ≤ 2 := by
    simpa using Nat.card_le_card_of_surjective (fun b : Bool => if b then (1 : F) else 0) hs
  have hl := Atlas.SuzukiFamily.card_ge_eight hcard hm
  omega

theorem shortRootParameter_central_second (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) (b : F) :
    shortRootParameters m hcard (0,b) ∈ Subgroup.center (shortRootSubgroup m hcard) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨⟨c,d⟩, rfl⟩ := (shortRootParameters m hcard).surjective g
  apply Subtype.ext
  exact shortRootPairEquiv_center_comm hcard c d b

/-- In the nonbinary admissible fields, centrality is exactly first coordinate zero. -/
theorem shortRootParameter_mem_center_iff (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (hm : 1 ≤ m) (a b : F) :
    shortRootParameters m hcard (a,b) ∈ Subgroup.center (shortRootSubgroup m hcard) ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    have hcomm := Subgroup.mem_center_iff.mp h
    have h1 := (shortRootParameter_commute_iff m hcard 1 0 a b).mp
      (hcomm (shortRootParameters m hcard (1,0)))
    have hat : theta F m a = a := by simpa using h1.symm
    obtain ⟨c, hc⟩ := exists_theta_ne_self m hcard hm
    have he := (shortRootParameter_commute_iff m hcard c 0 a b).mp
      (hcomm (shortRootParameters m hcard (c,0)))
    rw [hat, mul_comm a c] at he
    exact hc (mul_right_cancel₀ ha he)
  · rintro rfl
    exact shortRootParameter_central_second m hcard b

theorem shortRootSubgroup_noncommutative (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (hm : 1 ≤ m) :
    ∃ g h : shortRootSubgroup m hcard, g*h ≠ h*g := by
  obtain ⟨c, hc⟩ := exists_theta_ne_self m hcard hm
  refine ⟨shortRootParameters m hcard (1,0), shortRootParameters m hcard (c,0), ?_⟩
  intro he
  have h := (shortRootParameter_commute_iff m hcard 1 0 c 0).mp he
  exact hc (by simpa using h.symm)

end Atlas.ReeF4
