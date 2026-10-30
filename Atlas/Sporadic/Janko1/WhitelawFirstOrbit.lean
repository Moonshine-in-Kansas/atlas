import Atlas.Sporadic.Janko1.WhitelawPoints
import Mathlib.Data.Set.Card

/-!
Source-only candidate. The first seed has its actual H-stabilizer computed from
the monomial normal form: a squared-coordinate obstruction removes P,Q, and a
binary sign calculation leaves exactly two elements. This gives an 84-point
orbit and an upper bound of 1596 for the ten-orbit union, not equality.
-/
noncomputable section
namespace Atlas.Janko1

/-- The nonidentity sign change which scales the first seed by -1. -/
def firstSeedInvolution : H :=
  ⟨signElement ![0, 1, 1], signSubgroup_le_H (signElement_mem_signSubgroup _)⟩

theorem firstSeedInvolution_ne_one : firstSeedInvolution ≠ 1 := by
  intro h
  have ha : signElement ![0, 1, 1] = 1 := congrArg (fun x : H => (x : G2.Model Field)) h
  have hb : signHom (Multiplicative.ofAdd (![0, 1, 1] : SignParameters)) = signHom 1 :=
    ha.trans signHom.map_one.symm
  have hp := signHom_injective hb
  have h1 := congrArg (fun a : Multiplicative SignParameters => a.toAdd 1) hp
  exact (by decide : (1 : ZMod 2) ≠ 0) h1

theorem firstSeedInvolution_fixes :
    firstSeedInvolution • whitelawSeedPoint 0 = whitelawSeedPoint 0 := by
  change (signElement ![0, 1, 1]) •
    coordinatePoint (whitelawSeed 0) (whitelawSeed_ne_zero 0) =
      coordinatePoint (whitelawSeed 0) (whitelawSeed_ne_zero 0)
  rw [coordinatePoint_smul, coordinatePoint_eq_iff, imaginaryCoordinateAction_sign]
  exact ⟨-1, by decide⟩

set_option maxRecDepth 8192 in
/-- Only 21 coordinate permutations and 11 scalar values; no octonion/group enumeration.
Squaring has already removed every diagonal sign parameter. -/
theorem firstSeed_permutation_square_rigid :
    ∀ (i : Fin 7) (j : Fin 3) (c : Field),
      (∀ k : Fin 7,
        ((coordinateShift^[i.val] (coordinateDouble^[j.val] (whitelawSeed 0))) k) ^ 2 =
          c ^ 2 * (whitelawSeed 0 k) ^ 2) → i = 0 ∧ j = 0 := by
  decide

set_option maxRecDepth 8192 in
/-- Eight binary sign patterns and eleven scalar values, on just one seven-vector. -/
theorem firstSeed_sign_rigid : ∀ (a : SignParameters) (c : Field),
    (∀ k : Fin 7, signCharacter a k * whitelawSeed 0 k = c * whitelawSeed 0 k) →
      a = 0 ∨ a = ![0, 1, 1] := by
  decide

theorem firstSeed_normalForm_fixes_iff (t : SignParameters × (Fin 7 × Fin 3)) :
    (hNormalFormEquiv t : G2.Model Field) • whitelawSeedPoint 0 = whitelawSeedPoint 0 ↔
      t.2.1 = 0 ∧ t.2.2 = 0 ∧ (t.1 = 0 ∨ t.1 = ![0, 1, 1]) := by
  rcases t with ⟨a, i, j⟩
  constructor
  · intro h
    change (hNormalFormEquiv (a, i, j) : G2.Model Field) •
      coordinatePoint (whitelawSeed 0) (whitelawSeed_ne_zero 0) =
        coordinatePoint (whitelawSeed 0) (whitelawSeed_ne_zero 0) at h
    rw [coordinatePoint_smul, coordinatePoint_eq_iff] at h
    obtain ⟨c, hc⟩ := h
    rw [imaginaryCoordinateAction_normalForm] at hc
    have he (k : Fin 7) : signCharacter a k *
        (coordinateShift^[i.val] (coordinateDouble^[j.val] (whitelawSeed 0))) k =
          c * whitelawSeed 0 k := (congrFun hc k).symm
    have hs (k : Fin 7) :
        ((coordinateShift^[i.val] (coordinateDouble^[j.val] (whitelawSeed 0))) k) ^ 2 =
          c ^ 2 * (whitelawSeed 0 k) ^ 2 := by
      have hsign : signCharacter a k ^ 2 = 1 := by
        simpa only [pow_two] using signCharacter_square a k
      have hp := congrArg (fun z : Field => z ^ 2) (he k)
      erw [mul_pow, mul_pow, hsign, one_mul] at hp
      exact hp
    obtain ⟨hi, hj⟩ := firstSeed_permutation_square_rigid i j c hs
    refine ⟨hi, hj, ?_⟩
    subst i
    subst j
    apply firstSeed_sign_rigid a c
    simpa only [Fin.val_zero, Function.iterate_zero_apply] using he
  · rintro ⟨hi, hj, ha⟩
    dsimp only at hi hj ha
    subst i
    subst j
    rw [hNormalFormEquiv_apply]
    simp only [Fin.val_zero, pow_zero, mul_one]
    rcases ha with rfl | rfl
    · change signHom 1 • whitelawSeedPoint 0 = whitelawSeedPoint 0
      rw [map_one, one_smul]
    · exact firstSeedInvolution_fixes

theorem mem_firstSeed_stabilizer_iff (h : H) :
    h ∈ MulAction.stabilizer H (whitelawSeedPoint 0) ↔
      h = 1 ∨ h = firstSeedInvolution := by
  obtain ⟨⟨a, i, j⟩, rfl⟩ := hNormalFormEquiv.surjective h
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hf
    obtain ⟨hi, hj, ha⟩ := (firstSeed_normalForm_fixes_iff (a, i, j)).mp hf
    dsimp only at hi hj ha
    subst i
    subst j
    rcases ha with rfl | rfl
    · left
      apply Subtype.ext
      rw [hNormalFormEquiv_apply]
      simp only [Fin.val_zero, pow_zero, mul_one]
      change signHom 1 = 1
      exact signHom.map_one
    · right
      apply Subtype.ext
      rw [hNormalFormEquiv_apply]
      simp only [Fin.val_zero, pow_zero, mul_one, firstSeedInvolution]
  · rintro (h | h)
    · rw [h]
      exact one_smul H _
    · rw [h]
      exact firstSeedInvolution_fixes

theorem card_firstSeed_stabilizer :
    Nat.card (MulAction.stabilizer H (whitelawSeedPoint 0)) = 2 := by
  have hs : (MulAction.stabilizer H (whitelawSeedPoint 0) : Set H) =
      {1, firstSeedInvolution} := by
    ext h
    change h ∈ MulAction.stabilizer H (whitelawSeedPoint 0) ↔
      h = 1 ∨ h = firstSeedInvolution
    exact mem_firstSeed_stabilizer_iff h
  change Nat.card (MulAction.stabilizer H (whitelawSeedPoint 0) : Set H) = 2
  rw [Nat.card_coe_set_eq, hs, Set.ncard_pair firstSeedInvolution_ne_one.symm]

theorem card_firstWhitelawOrbit : Nat.card (whitelawOrbit 0) = 84 := by
  have h := whitelawOrbit_card_mul_stabilizer 0
  rw [card_firstSeed_stabilizer] at h
  omega

/-- A cover, not a disjoint-union equivalence. -/
def whitelawOrbitCover : (Σ r : Fin 10, whitelawOrbit r) → WhitelawPoints :=
  fun x => ⟨x.2.val, x.1, x.2.property⟩

theorem whitelawOrbitCover_surjective : Function.Surjective whitelawOrbitCover := by
  rintro ⟨p, r, hr⟩
  exact ⟨⟨r, ⟨p, hr⟩⟩, rfl⟩

/-- The lower bound still requires the nine trivial stabilizers and orbit disjointness. -/
theorem card_whitelawPoints_le : Nat.card WhitelawPoints ≤ 1596 := by
  have hc := Nat.card_le_card_of_surjective whitelawOrbitCover whitelawOrbitCover_surjective
  rw [Nat.card_sigma] at hc
  have hs : (∑ r : Fin 10, Nat.card (whitelawOrbit r)) ≤ 1596 := by
    calc
      _ ≤ ∑ r : Fin 10, if r = 0 then 84 else 168 := by
        apply Finset.sum_le_sum
        intro r _
        by_cases hr : r = 0
        · subst r
          rw [if_pos rfl, card_firstWhitelawOrbit]
        · rw [if_neg hr]
          exact card_whitelawOrbit_le r
      _ = 1596 := by decide
  exact hc.trans hs

end Atlas.Janko1
