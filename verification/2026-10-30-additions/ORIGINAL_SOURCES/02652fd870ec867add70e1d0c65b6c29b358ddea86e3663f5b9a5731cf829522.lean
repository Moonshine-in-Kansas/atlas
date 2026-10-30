import Atlas.LinearGroups.ReeG2.SmallParameter
import Mathlib.GroupTheory.OrderOfElement

/-!
Source-only draft, 27 October 2026. No build or audit has been run.

Concrete small-parameter generators inside the retained seven-dimensional
matrix group. No semilinear identification or Ree derived-subgroup assertion
is used or claimed here.
-/

noncomputable section
namespace Atlas.Comparisons.ReeThree.Boundary
open Atlas.ReeG2

variable {F : Type*} [Field F] [Finite F] [CharP F 3]

theorem cube_eq (hF : Nat.card F = 3) (x : F) : x ^ 3 = x := by
  simpa [theta_apply] using
    theta_square_cube (m := 0) (smallParameter_card_condition hF) x

theorem scalar_cases (hF : Nat.card F = 3) (x : F) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hx : x * (x - 1) * (x + 1) = 0 := by
    calc
      _ = x ^ 3 - x := by ring
      _ = 0 := by rw [cube_eq hF]; exact sub_self x
  rcases mul_eq_zero.mp hx with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · right; right
    linear_combination h

theorem unit_cases (hF : Nat.card F = 3) (l : Fˣ) : l = 1 ∨ l = -1 := by
  rcases scalar_cases hF (l : F) with h | h | h
  · exact False.elim (Units.ne_zero l h)
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext h)

theorem root_mul (hF : Nat.card F = 3) (a b c d e f : F) :
    rootElement 0 a b c * rootElement 0 d e f =
      rootElement 0 (a + d) (b + e - a * d)
        (c + f - d * b + a * d ^ 2 - a ^ 2 * d) := by
  simpa [theta_apply, cube_eq hF, pow_two, mul_assoc] using
    rootElement_mul 0 (smallParameter_card_condition hF) a b c d e f

theorem root_inv (hF : Nat.card F = 3) (a b c : F) :
    (rootElement 0 a b c)⁻¹ =
      rootElement 0 (-a) (-(b + a ^ 2)) (-(c + a * b - a)) := by
  have ha : a ^ 2 * a = a := by rw [← pow_succ, cube_eq hF]
  simpa only [theta_apply, pow_zero, pow_one, cube_eq hF, ← pow_two, ha] using
    rootElement_inv 0 (smallParameter_card_condition hF) a b c

/-- The prospective nonsplit-torus generator is alpha(1) beta(1), not alpha(1). -/
def u : Ambient F := rootElement 0 1 1 0
def v : Ambient F := rootElement 0 0 1 0
def t : Ambient F := torus 0 (-1)

theorem u_eq_alpha_beta : (u : Ambient F) = alpha 0 1 * beta 0 1 := by
  simp [u, rootElement]

theorem v_eq_beta : (v : Ambient F) = beta 0 1 := by
  simp [v, rootElement]

theorem u_square (hF : Nat.card F = 3) :
    (u : Ambient F) ^ 2 = rootElement 0 (-1) 1 (-1) := by
  rw [pow_two, u, root_mul hF]
  congr 1 <;> ring_nf <;> reduce_mod_char!

theorem u_cube (hF : Nat.card F = 3) :
    (u : Ambient F) ^ 3 = rootElement 0 0 0 (-1) := by
  rw [pow_succ, u_square hF, u, root_mul hF]
  congr 1 <;> ring_nf <;> reduce_mod_char!

theorem u_fourth (hF : Nat.card F = 3) :
    (u : Ambient F) ^ 4 = rootElement 0 1 1 (-1) := by
  rw [pow_succ, u_cube hF, u, root_mul hF]
  simp

theorem u_sixth (hF : Nat.card F = 3) :
    (u : Ambient F) ^ 6 = rootElement 0 0 0 1 := by
  rw [show 6 = 3 * 2 by decide, pow_mul, u_cube hF, pow_two, root_mul hF]
  congr 1 <;> ring_nf <;> reduce_mod_char!

theorem u_ninth (hF : Nat.card F = 3) : (u : Ambient F) ^ 9 = 1 := by
  rw [show 9 = 6 + 3 by decide, pow_add, u_sixth hF, u_cube hF, root_mul hF]
  simpa using rootElement_zero (F := F) 0

theorem u_inv (hF : Nat.card F = 3) :
    (u : Ambient F)⁻¹ = rootElement 0 (-1) 1 0 := by
  rw [u, root_inv hF]
  congr 1 <;> ring_nf <;> reduce_mod_char!

theorem u_order (hF : Nat.card F = 3) : orderOf (u : Ambient F) = 9 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hn : (u : Ambient F) ^ 3 ≠ 1 := by
    intro h
    rw [u_cube hF, ← rootElement_zero (F := F) 0] at h
    have hc := congrArg (fun g : Ambient F => g.val 0 3) h
    simp only [rootElement_val, rootMatrix_03, theta_apply, pow_zero, pow_one,
      zero_mul, sub_zero, zero_sub, neg_neg] at hc
    exact one_ne_zero hc
  exact orderOf_eq_prime_pow (p := 3) (n := 1) hn (u_ninth hF)

theorem v_square (hF : Nat.card F = 3) :
    (v : Ambient F) ^ 2 = rootElement 0 0 (-1) 0 := by
  rw [pow_two, v, root_mul hF]
  congr 1 <;> ring_nf <;> reduce_mod_char!

theorem v_cube (hF : Nat.card F = 3) : (v : Ambient F) ^ 3 = 1 := by
  rw [pow_succ, v_square hF, v, root_mul hF]
  simpa using rootElement_zero (F := F) 0

theorem v_inv (hF : Nat.card F = 3) :
    (v : Ambient F)⁻¹ = rootElement 0 0 (-1) 0 := by
  rw [v, root_inv hF]
  simp

theorem v_order (hF : Nat.card F = 3) : orderOf (v : Ambient F) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime (v_cube hF)
  intro h
  change rootElement 0 0 1 0 = 1 at h
  rw [← rootElement_zero (F := F) 0] at h
  have hc := congrArg (fun g : Ambient F => g.val 0 2) h
  simp only [rootElement_val, rootMatrix_02, theta_apply, pow_zero, pow_one,
    neg_zero] at hc
  exact neg_ne_zero.mpr one_ne_zero hc

theorem t_square : (t : Ambient F) * t = 1 := by
  change torus 0 (-1 : Fˣ) * torus 0 (-1) = 1
  rw [← torus_mul, neg_mul_neg, one_mul]
  exact (torusHom (F := F) 0).map_one

theorem t_inv : (t : Ambient F)⁻¹ = t := inv_eq_of_mul_eq_one_right t_square

theorem t_order : orderOf (t : Ambient F) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime (by simpa [pow_two] using (t_square (F := F)))
  intro h
  have h1 : torus 0 (-1 : Fˣ) = torus 0 1 :=
    h.trans (torusHom (F := F) 0).map_one.symm
  have hu := congrArg (fun l : Fˣ => (l : F)) (torus_injective 0 h1)
  change (-1 : F) = 1 at hu
  have hz : (1 : F) = 0 := by
    linear_combination (CharP.cast_eq_zero F 3) + hu
  exact one_ne_zero hz

/-- Conjugation by beta(1) acts as the fourth-power automorphism of <u>. -/
theorem v_conjugate_u (hF : Nat.card F = 3) :
    (v : Ambient F) * u * v⁻¹ = u ^ 4 := by
  rw [u_fourth hF, v_inv hF]
  change rootElement 0 0 1 0 * rootElement 0 1 1 0 *
    rootElement 0 0 (-1) 0 = rootElement 0 1 1 (-1)
  rw [root_mul hF, root_mul hF]
  congr 1 <;> ring_nf <;> reduce_mod_char!

/-- The minus-one diagonal matrix inverts this precise cyclic subgroup. -/
theorem t_conjugate_u (hF : Nat.card F = 3) :
    (t : Ambient F) * u * t⁻¹ = u⁻¹ := by
  have h := torus_conjugate_root (F := F) 0
    (smallParameter_card_condition hF) (-1) 1 1 0
  rw [u_inv hF, t_inv]
  simpa [t, u, torus_inv, theta_apply, cube_eq hF] using h

theorem t_commutes_v (hF : Nat.card F = 3) :
    (t : Ambient F) * v = v * t := by
  have h := torus_conjugate_root (F := F) 0
    (smallParameter_card_condition hF) (-1) 0 1 0
  have hc : (t : Ambient F) * v * t = v := by
    simpa only [t, v, torus_inv, inv_neg, inv_one, theta_apply, pow_zero,
      pow_one, Units.val_neg, Units.val_one, cube_eq hF, zero_mul, mul_zero,
      mul_one, one_mul, zero_div, neg_div_neg_eq, one_div, inv_one] using h
  calc
    t * v = (t * v * t) * t := by simp only [mul_assoc, t_square, mul_one]
    _ = v * t := by rw [hc]

/-- Two actual root matrices generate the entire order-27 unipotent subgroup. -/
theorem rootSubgroup_eq_pair (hF : Nat.card F = 3) :
    rootSubgroup 0 (smallParameter_card_condition hF) =
      Subgroup.closure ({u, v} : Set (Ambient F)) := by
  let H := Subgroup.closure ({u, v} : Set (Ambient F))
  have hu : (u : Ambient F) ∈ H := Subgroup.subset_closure (by simp)
  have hv : (v : Ambient F) ∈ H := Subgroup.subset_closure (by simp)
  have ha : ∀ a : F, alpha 0 a ∈ H := by
    intro a
    rcases scalar_cases hF a with rfl | rfl | rfl
    · simpa using H.one_mem
    · have he : alpha (F := F) 0 1 = u * v⁻¹ := by
        rw [v_inv hF, u, root_mul hF]
        simp [rootElement]
      rw [he]
      exact H.mul_mem hu (H.inv_mem hv)
    · have he : alpha (F := F) 0 (-1) = u⁻¹ * v⁻¹ := by
        rw [u_inv hF, v_inv hF, root_mul hF]
        simp [rootElement]
      rw [he]
      exact H.mul_mem (H.inv_mem hu) (H.inv_mem hv)
  have hb : ∀ b : F, beta 0 b ∈ H := by
    intro b
    rcases scalar_cases hF b with rfl | rfl | rfl
    · simpa using H.one_mem
    · simpa [v, rootElement] using hv
    · simpa [v_inv hF, rootElement] using H.inv_mem hv
  have hc : ∀ c : F, gamma 0 c ∈ H := by
    intro c
    rcases scalar_cases hF c with rfl | rfl | rfl
    · simpa using H.one_mem
    · simpa [u_sixth hF, rootElement] using H.pow_mem hu 6
    · simpa [u_cube hF, rootElement] using H.pow_mem hu 3
  apply le_antisymm
  · rintro g ⟨⟨a, b, c⟩, rfl⟩
    exact H.mul_mem (H.mul_mem (ha a) (hb b)) (hc c)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(1, 1, 0), rfl⟩
    · exact ⟨(0, 1, 0), rfl⟩

/-- The retained point stabilizer is generated by u, beta(1), and h(-1). -/
theorem borel_eq_triple (hF : Nat.card F = 3) :
    borel 0 (smallParameter_card_condition hF) =
      Subgroup.closure ({u, v, t} : Set (Ambient F)) := by
  apply le_antisymm
  · apply sup_le
    · rw [rootSubgroup_eq_pair hF]
      apply Subgroup.closure_mono
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      rcases hg with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro g ⟨l, rfl⟩
      rcases unit_cases hF l with rfl | rfl
      · change torus 0 (1 : Fˣ) ∈ Subgroup.closure ({u, v, t} : Set (Ambient F))
        rw [show torus 0 (1 : Fˣ) = 1 from (torusHom (F := F) 0).map_one]
        exact (Subgroup.closure _).one_mem
      · exact Subgroup.subset_closure (by simp [t, torusHom])
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact (show rootSubgroup 0 (smallParameter_card_condition hF) ≤
          borel 0 (smallParameter_card_condition hF) from le_sup_left) ⟨(1, 1, 0), rfl⟩
    · exact (show rootSubgroup 0 (smallParameter_card_condition hF) ≤
          borel 0 (smallParameter_card_condition hF) from le_sup_left) ⟨(0, 1, 0), rfl⟩
    · exact (show splitTorus (F := F) 0 ≤
          borel 0 (smallParameter_card_condition hF) from le_sup_right) ⟨-1, rfl⟩

/-- These three stabilizer generators and the retained Weyl matrix generate
the full retained Ree group, with no order-based recognition. -/
theorem generated_eq_four (hF : Nat.card F = 3) :
    generated F 0 = Subgroup.closure ({u, v, t, upsilon} : Set (Ambient F)) := by
  let H := Subgroup.closure ({u, v, t, upsilon} : Set (Ambient F))
  have hb : borel 0 (smallParameter_card_condition hF) ≤ H := by
    rw [borel_eq_triple hF]
    apply Subgroup.closure_mono
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hr : rootSubgroup 0 (smallParameter_card_condition hF) ≤ H :=
    le_trans le_sup_left hb
  have ht : splitTorus (F := F) 0 ≤ H := le_trans le_sup_right hb
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (((⟨a, rfl⟩ | ⟨b, rfl⟩) | ⟨c, rfl⟩) | ⟨l, rfl⟩) | hw
    · apply hr
      exact ⟨(a, 0, 0), by simp [rootElement]⟩
    · apply hr
      exact ⟨(0, b, 0), by simp [rootElement]⟩
    · apply hr
      exact ⟨(0, 0, c), by simp [rootElement]⟩
    · exact ht ⟨l, rfl⟩
    · have hg : g = upsilon := Set.mem_singleton_iff.mp hw
      subst g
      exact Subgroup.subset_closure (by simp)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact rootSubgroup_le_generated 0 (smallParameter_card_condition hF)
        ⟨(1, 1, 0), rfl⟩
    · exact rootSubgroup_le_generated 0 (smallParameter_card_condition hF)
        ⟨(0, 1, 0), rfl⟩
    · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨-1, rfl⟩))
    · exact upsilon_mem_generated 0

end Atlas.Comparisons.ReeThree.Boundary
