import Atlas.LinearGroups.Chevalley.RootData.ClassicalBAxisChain
import Atlas.LinearGroups.Chevalley.RootData.ParabolicCosetDecomposition

/-! Constructive minimal right-parabolic representatives for the actual B
Weyl image. The path uses adjacent coordinate swaps and the terminal sign
flip. The exact lengths follow from the orbit-distance lower bound. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalBParabolic
open Classical ClassicalData RootData

theorem axisHeight_injective (n : ℕ) : Function.Injective (axisHeight n) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hi := i.isLt
  have hj := j.isLt
  cases b <;> cases c
  · have hv' : i.val = j.val := by
      simp only [axisHeight, Bool.false_eq_true, ↓reduceIte] at h
      omega
    exact Prod.ext (Fin.ext hv') rfl
  · simp only [axisHeight, Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at h
    omega
  · simp only [axisHeight, Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at h
    omega
  · have hv : i.val = j.val := by simpa only [axisHeight, Bool.true_eq, ↓reduceIte] using h
    exact Prod.ext (Fin.ext hv) rfl

/-- The next simple reflection along the signed-axis line. The terminal
negative first axis is excluded from the forward-step theorem below. -/
def axisForwardIndex (n : ℕ) (c : Fin (n + 1) × Bool) : Fin (n + 1) :=
  if c.2 then c.1 else ⟨c.1.val - 1, by have h := c.1.isLt; omega⟩

theorem axisHeight_forward (n : ℕ) (c : Fin (n + 1) × Bool)
    (hc : axisHeight n c < 2 * n + 1) :
    axisHeight n (axisStep n (axisForwardIndex n c) c) = axisHeight n c + 1 := by
  have hbound := c.1.isLt
  cases hb : c.2 with
  | true =>
    by_cases hlast : c.1.val < n
    · simp [axisForwardIndex, hb, axisStep, hlast, axisHeight]
    · have hval : c.1.val = n := by omega
      simp [axisForwardIndex, hb, axisStep, hlast, axisHeight, hval] <;> omega
  | false =>
    have hpos : 0 < c.1.val := by
      simp only [axisHeight, hb, Bool.false_eq_true, ↓reduceIte] at hc
      omega
    let i : Fin (n + 1) := ⟨c.1.val - 1, by omega⟩
    have hi : i.val < n := by dsimp only [i]; omega
    have hnext : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = c.1 := by
      apply Fin.ext
      dsimp only [i]
      omega
    change axisHeight n (axisStep n (if c.2 then c.1 else
      ⟨c.1.val - 1, by omega⟩) c) = _
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    change axisHeight n (axisStep n i c) = _
    simp only [axisStep, hi, dite_true]
    rw [hnext, Equiv.swap_apply_right]
    simp only [axisHeight, hb, Bool.false_eq_true, ↓reduceIte]
    dsimp only [i]
    omega

/-- A deterministic path word and its actual signed-axis label. -/
def axisPath (n : ℕ) : ℕ → List (Fin (n + 1)) × (Fin (n + 1) × Bool)
  | 0 => ([], (0, true))
  | k + 1 =>
    let p := axisPath n k
    let i := axisForwardIndex n p.2
    (i :: p.1, axisStep n i p.2)

theorem axisPath_word_length (n k : ℕ) : (axisPath n k).1.length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [axisPath, List.length_cons] using congrArg Nat.succ ih

theorem axisPath_height (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    axisHeight n (axisPath n k).2 = k := by
  induction k with
  | zero => simp [axisPath, axisHeight]
  | succ k ih =>
    have ih' := ih (by omega)
    change axisHeight n (axisStep n (axisForwardIndex n (axisPath n k).2)
      (axisPath n k).2) = k + 1
    rw [axisHeight_forward n _ (by rw [ih']; omega), ih']

theorem axisPath_action (n k : ℕ) :
    simpleReflectionWord (pairingB (n + 1)) (baseB n)
      ((axisPath n k).1.map (simple n)) (seed n) = decodeShort (axisPath n k).2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [axisPath, List.map_cons, simpleReflectionWord_cons,
      Equiv.Perm.mul_apply, ih, simple_reflection_axis]

def pathRepresentative (n : ℕ) (k : Fin (2 * (n + 1))) : W n :=
  rootWeylWord (pairingB (n + 1)) (baseB n) ((axisPath n k.val).1.map (simple n))

theorem pathRepresentative_seed (n : ℕ) (k : Fin (2 * (n + 1))) :
    (pathRepresentative n k).val (seed n) = decodeShort (axisPath n k.val).2 := by
  rw [pathRepresentative, rootWeylWord_val]
  exact axisPath_action n k.val

theorem pathRepresentative_length (n : ℕ) (k : Fin (2 * (n + 1))) :
    rootWeylLength (pairingB (n + 1)) (baseB n) (pathRepresentative n k) = k.val := by
  apply Nat.le_antisymm
  · have h := rootWeylWord_length_le (pairingB (n + 1)) (baseB n)
      ((axisPath n k.val).1.map (simple n))
    simpa only [pathRepresentative, List.length_map, axisPath_word_length] using h
  · have h := axisHeight_le_rootWeylLength n (pathRepresentative n k)
      (axisPath n k.val).2 (pathRepresentative_seed n k)
    rw [axisPath_height n k.val (by have := k.isLt; omega)] at h
    exact h

/-- The actual length-additive parabolic split and orbit-distance bound force
the parabolic factor of this path representative to be the identity. -/
theorem pathRepresentative_minimal (n : ℕ) (k : Fin (2 * (n + 1))) :
    ∀ i ∈ J n, (baseB n).IsPos ((pathRepresentative n k).val i.val) := by
  let p := (rootParabolicProductEquiv (pairingB (n + 1)) (baseB n) (J n)).symm
    (pathRepresentative n k)
  have hp : p.1.val * p.2.val = pathRepresentative n k :=
    (rootParabolicProductEquiv (pairingB (n + 1)) (baseB n) (J n)).apply_symm_apply _
  have hfix := (fixes_seed_iff_parabolic n p.2.val).mpr p.2.property
  have hseed : p.1.val.val (seed n) = decodeShort (axisPath n k.val).2 := by
    have he := congrArg (fun w : W n => w.val (seed n)) hp
    change p.1.val.val (p.2.val.val (seed n)) = _ at he
    simpa only [hfix, pathRepresentative_seed] using he
  have hbound := axisHeight_le_rootWeylLength n p.1.val (axisPath n k.val).2 hseed
  rw [axisPath_height n k.val (by have := k.isLt; omega)] at hbound
  have hlen := rootParabolicProductEquiv_length (pairingB (n + 1)) (baseB n) (J n) p
  change rootWeylLength (pairingB (n + 1)) (baseB n) (p.1.val * p.2.val) = _ at hlen
  rw [hp, pathRepresentative_length] at hlen
  have hv0 : rootWeylLength (pairingB (n + 1)) (baseB n) p.2.val = 0 := by omega
  have hv1 := (rootWeylLength_eq_zero_iff (pairingB (n + 1)) (baseB n) p.2.val).mp hv0
  have hx : p.1.val = pathRepresentative n k := by simpa only [hv1, mul_one] using hp
  simpa only [hx] using p.1.property

def pathRepresentativeMap (n : ℕ) :
    Fin (2 * (n + 1)) → rootParabolicRepresentatives (pairingB (n + 1)) (baseB n) (J n) :=
  fun k => ⟨pathRepresentative n k, pathRepresentative_minimal n k⟩

theorem pathRepresentativeMap_bijective (n : ℕ) : Function.Bijective (pathRepresentativeMap n) := by
  constructor
  · intro k l h
    have hval := congrArg (fun x : rootParabolicRepresentatives (pairingB (n + 1)) (baseB n) (J n) =>
      rootWeylLength (pairingB (n + 1)) (baseB n) x.val) h
    apply Fin.ext
    simpa only [pathRepresentativeMap, pathRepresentative_length] using hval
  · intro x
    obtain ⟨c, hc⟩ := seed_image_signed n x.val
    let k : Fin (2 * (n + 1)) := ⟨axisHeight n c, axisHeight_lt n c⟩
    have hk : (axisPath n k.val).2 = c := axisHeight_injective n (by
      rw [axisPath_height n k.val (by have := k.isLt; omega)])
    have hseed : (pathRepresentative n k).val (seed n) = x.val.val (seed n) := by
      rw [pathRepresentative_seed, hk, hc]
    have hfix : ((pathRepresentative n k)⁻¹ * x.val).val (seed n) = seed n := by
      change (pathRepresentative n k).val.symm (x.val.val (seed n)) = seed n
      rw [← hseed]
      exact (pathRepresentative n k).val.symm_apply_apply (seed n)
    have he := rootWeyl_parabolic_minimal_unique (pairingB (n + 1)) (baseB n) (J n)
      (pathRepresentative n k) x.val (pathRepresentative_minimal n k) x.property
      ((fixes_seed_iff_parabolic n _).mp hfix)
    exact ⟨k, Subtype.ext he⟩

def pathRepresentativeEquiv (n : ℕ) :
    Fin (2 * (n + 1)) ≃ rootParabolicRepresentatives (pairingB (n + 1)) (baseB n) (J n) :=
  Equiv.ofBijective (pathRepresentativeMap n) (pathRepresentativeMap_bijective n)

theorem pathRepresentativeEquiv_length (n : ℕ) (k : Fin (2 * (n + 1))) :
    rootWeylLength (pairingB (n + 1)) (baseB n) (pathRepresentativeEquiv n k).val = k.val :=
  pathRepresentative_length n k

end Atlas.Chevalley.ClassicalBParabolic
