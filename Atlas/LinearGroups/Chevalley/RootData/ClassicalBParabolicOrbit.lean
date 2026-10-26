import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC
import Atlas.LinearGroups.Chevalley.RootData.DominantFunctionalStabilizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel

/-! The first-coordinate orbit and its actual stabilizer in the integral B
Weyl permutation image. The orbit consists of precisely the two signed axes
per coordinate. Its stabilizer is the parabolic omitting the first simple
root. A lower-rank isomorphism and minimal representative lengths are not
assumed or asserted in this module. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalBParabolic
open Classical ClassicalData RootData

abbrev W (n : ℕ) := (pairingB (n + 1)).weylGroupToPerm.range
abbrev simple (n : ℕ) (i : Fin (n + 1)) := baseBIndexEquiv n i
def seed (n : ℕ) : BRoot (n + 1) := shortRoot 0 1 (Or.inl rfl)
def J (n : ℕ) : Finset (baseB n).support := Finset.univ.erase (simple n 0)

def coordinateFunctional (n : ℕ) : (pairingB (n + 1)).rootSpan ℤ →+ ℚ where
  toFun x := 2 * (x.val 0 : ℚ)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

private theorem chainVector_first (n : ℕ) (i : Fin (n + 1)) :
    chainVector n 1 i 0 = if i = 0 then 1 else 0 := by
  by_cases hi : i.val < n
  · have hnext : (0 : Fin (n + 1)) ≠ ⟨i.val + 1, by omega⟩ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_mk] at hv
      omega
    simp [chainVector, hi, Pi.single_apply, hnext, eq_comm]
  · simp [chainVector, hi, Pi.single_apply, eq_comm]

theorem coordinateFunctional_simple (n : ℕ) (i : Fin (n + 1)) :
    coordinateFunctional n ((pairingB (n + 1)).rootSpanMem ℤ (simple n i).val) =
      if i = 0 then 2 else 0 := by
  change 2 * ((simpleB n i).val 0 : ℚ) = _
  rw [simpleB_vector, chainVector_first]
  split_ifs <;> norm_num

private theorem coordinateFunctional_dominant (n : ℕ) (i : (baseB n).support) :
    0 ≤ coordinateFunctional n ((pairingB (n + 1)).rootSpanMem ℤ i.val) := by
  obtain ⟨k, rfl⟩ := (baseBIndexEquiv n).surjective i
  rw [coordinateFunctional_simple]
  split_ifs <;> norm_num

private theorem coordinateFunctional_zero_simple (n : ℕ) :
    rootFunctionalZeroSimple (pairingB (n + 1)) (baseB n) (coordinateFunctional n) = J n := by
  ext i
  obtain ⟨k, rfl⟩ := (baseBIndexEquiv n).surjective i
  simp only [rootFunctionalZeroSimple, Finset.mem_filter, Finset.mem_univ, true_and,
    coordinateFunctional_simple, J, Finset.mem_erase, and_true]
  simp only [simple, (baseBIndexEquiv n).injective.eq_iff]
  split_ifs <;> simp_all

private theorem coordinateFunctional_root (n : ℕ) (β : BRoot (n + 1)) :
    coordinateFunctional n ((pairingB (n + 1)).rootSpanMem ℤ β) =
      ((pairingB (n + 1)).pairing β (seed n) : ℚ) := by
  change 2 * (β.val 0 : ℚ) = (coroot (shortRoot 0 1 (Or.inl rfl)) β.val : ℚ)
  rw [coroot_short]
  norm_num

private theorem weyl_pairing (n : ℕ) (w : W n) (α β : BRoot (n + 1)) :
    (pairingB (n + 1)).pairing (w.val α) (w.val β) =
      (pairingB (n + 1)).pairing α β := by
  obtain ⟨g, hg⟩ := w.property
  have hp := g.val.toHom.pairing (i := α) (j := β)
  change (pairingB (n + 1)).pairing
    ((pairingB (n + 1)).weylGroupToPerm g α)
    ((pairingB (n + 1)).weylGroupToPerm g β) = _ at hp
  simpa only [hg] using hp

private theorem pairing_detects_seed (n : ℕ) (β : BRoot (n + 1))
    (h : ∀ α, (pairingB (n + 1)).pairing α β =
      (pairingB (n + 1)).pairing α (seed n)) : β = seed n := by
  apply coroot_injective
  apply (Pi.basisFun ℤ (Fin (n + 1))).ext
  intro k
  rw [Pi.basisFun_apply]
  exact h (shortRoot k 1 (Or.inl rfl))

/-- Actual seed stabilizer, with no subgroup identification supplied by a caller. -/
theorem fixes_seed_iff_parabolic (n : ℕ) (w : W n) :
    w.val (seed n) = seed n ↔ w ∈ rootParabolicSubgroup (pairingB (n + 1)) (baseB n) (J n) := by
  have heq := rootFunctionalStabilizer_eq_parabolic (pairingB (n + 1)) (baseB n)
    (coordinateFunctional n) (coordinateFunctional_dominant n)
  rw [coordinateFunctional_zero_simple] at heq
  rw [← heq]
  constructor
  · intro hw β
    rw [coordinateFunctional_root, coordinateFunctional_root]
    exact congrArg (fun z : ℤ => (z : ℚ)) (by
      simpa only [hw] using weyl_pairing n w β (seed n))
  · intro hw
    apply pairing_detects_seed
    intro α
    have hfun := hw ((w⁻¹).val α)
    have hinv : w.val ((w⁻¹).val α) = α := w.val.apply_symm_apply α
    rw [coordinateFunctional_root, coordinateFunctional_root, hinv] at hfun
    have hcast : (pairingB (n + 1)).pairing α (seed n) =
        (pairingB (n + 1)).pairing ((w⁻¹).val α) (seed n) := Int.cast_injective hfun
    have hp := weyl_pairing n w ((w⁻¹).val α) (seed n)
    rw [hinv] at hp
    exact hp.trans hcast.symm

private theorem weyl_norm (n : ℕ) (w : W n) (β : BRoot (n + 1)) :
    dot (w.val β).val (w.val β).val = dot β.val β.val := by
  obtain ⟨l, hl⟩ := exists_simpleReflectionWord_of_mem (pairingB (n + 1)) (baseB n) w.property
  have hword : ∀ l : List (baseB n).support,
      dot (simpleReflectionWord (pairingB (n + 1)) (baseB n) l β).val
          (simpleReflectionWord (pairingB (n + 1)) (baseB n) l β).val = dot β.val β.val := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      change dot (reflect i.val (simpleReflectionWord (pairingB (n + 1)) (baseB n) l β).val)
        (reflect i.val (simpleReflectionWord (pairingB (n + 1)) (baseB n) l β).val) = _
      rw [reflect_norm, ih]
  simpa only [hl] using hword l

theorem seed_image_signed (n : ℕ) (w : W n) :
    ∃ c : Fin (n + 1) × Bool, w.val (seed n) = decodeShort c := by
  have hn : dot (w.val (seed n)).val (w.val (seed n)).val = 1 := by
    rw [weyl_norm]
    simp [seed, shortRoot, dot, Pi.single_apply]
  obtain ⟨c, hc⟩ := decodeB_surjective (w.val (seed n))
  cases c with
  | inl c => exact ⟨c, hc.symm⟩
  | inr c =>
    rw [← hc] at hn
    change dot c.val c.val = 1 at hn
    rcases c.property with ⟨hfalse, _⟩ | htwo
    · cases hfalse
    · omega

private def rootReflection (n : ℕ) (α : BRoot (n + 1)) : W n :=
  ⟨(pairingB (n + 1)).reflectionPerm α, by
    change (pairingB (n + 1)).reflectionPerm α ∈
      (pairingB (n + 1)).weylGroupToPerm.range
    rw [(pairingB (n + 1)).range_weylGroupToPerm]
    exact Subgroup.subset_closure ⟨α, rfl⟩⟩

private theorem reflect_difference_axis {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    reflect (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl))
      (Pi.single i 1) = Pi.single j 1 := by
  have hdot : dot (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)).val
      (Pi.single i 1) = 1 := by
    simp [longRoot, dot_add_left, dot_single_left, Pi.single_apply, hij, Ne.symm hij]
  simp only [reflect, long_scale, hdot, one_mul, one_smul]
  change (Pi.single i (1 : ℤ) : Lattice r) - (Pi.single i 1 + Pi.single j (-1)) = Pi.single j 1
  rw [Pi.single_neg]
  abel

private theorem positive_axis_reachable (n : ℕ) (k : Fin (n + 1)) :
    ∃ w : W n, w.val (seed n) = shortRoot k 1 (Or.inl rfl) := by
  by_cases hk : k = 0
  · subst k
    exact ⟨1, rfl⟩
  · refine ⟨rootReflection n (longRoot true 0 k (Ne.symm hk)
      1 (-1) (Or.inl rfl) (Or.inr rfl)), ?_⟩
    apply Subtype.ext
    exact reflect_difference_axis 0 k (Ne.symm hk)

theorem signed_axis_reachable (n : ℕ) (c : Fin (n + 1) × Bool) :
    ∃ w : W n, w.val (seed n) = decodeShort c := by
  obtain ⟨w, hw⟩ := positive_axis_reachable n c.1
  cases hc : c.2 with
  | true => exact ⟨w, by simpa only [decodeShort, hc, ite_true] using hw⟩
  | false =>
    refine ⟨rootReflection n (shortRoot c.1 1 (Or.inl rfl)) * w, ?_⟩
    change (pairingB (n + 1)).reflectionPerm (shortRoot c.1 1 (Or.inl rfl))
      (w.val (seed n)) = _
    rw [hw]
    apply Subtype.ext
    funext k
    change reflect (shortRoot c.1 1 (Or.inl rfl)) (Pi.single c.1 1) k =
      (decodeShort c).val k
    rw [reflect_short]
    by_cases hk : k = c.1 <;> simp [decodeShort, hc, shortRoot, Pi.single_apply, hk]

/-- The actual orbit as a subtype of the original integer root labels. -/
def SeedOrbit (n : ℕ) := {β : BRoot (n + 1) // ∃ w : W n, w.val (seed n) = β}

def signedAxisOrbitEquiv (n : ℕ) : (Fin (n + 1) × Bool) ≃ SeedOrbit n :=
  Equiv.ofBijective (fun c => ⟨decodeShort c, signed_axis_reachable n c⟩)
    ⟨by intro c d h; exact decodeShort_injective (congrArg Subtype.val h), by
      intro β
      obtain ⟨w, hw⟩ := β.property
      obtain ⟨c, hc⟩ := seed_image_signed n w
      exact ⟨c, Subtype.ext (hc.symm.trans hw)⟩⟩

theorem seedOrbit_card (n : ℕ) : Nat.card (SeedOrbit n) = 2 * (n + 1) := by
  rw [← Nat.card_congr (signedAxisOrbitEquiv n), Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Nat.mul_comm]

end Atlas.Chevalley.ClassicalBParabolic
