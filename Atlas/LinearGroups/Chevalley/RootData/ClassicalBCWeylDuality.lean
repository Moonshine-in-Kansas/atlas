import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC
import Atlas.LinearGroups.Chevalley.RootData.RootWeylPoincare

/-! The actual B and C integral root pairings have the same root-label
reflection permutations. Their Weyl images and shortest simple-word lengths
therefore agree, without identifying either constructed linear group. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalData
open Classical RootData

theorem weylImage_B_eq_C (r : ℕ) :
    (pairingB r).weylGroupToPerm.range = (pairingC r).weylGroupToPerm.range := by
  rw [(pairingB r).range_weylGroupToPerm, (pairingC r).range_weylGroupToPerm]
  rfl

/-- Identity on the actual root permutations, between the dual Weyl images. -/
def weylBCEquiv (r : ℕ) :
    (pairingB r).weylGroupToPerm.range ≃* (pairingC r).weylGroupToPerm.range :=
  MulEquiv.subgroupCongr (weylImage_B_eq_C r)

@[simp] theorem weylBCEquiv_val (r : ℕ) (w : (pairingB r).weylGroupToPerm.range) :
    (weylBCEquiv r w).val = w.val := rfl

theorem weylBCEquiv_length (n : ℕ) (w : (pairingB (n + 1)).weylGroupToPerm.range) :
    rootWeylLength (pairingC (n + 1)) (baseC n) (weylBCEquiv (n + 1) w) =
      rootWeylLength (pairingB (n + 1)) (baseB n) w := by
  apply Nat.le_antisymm
  · obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec (pairingB (n + 1)) (baseB n) w
    have hc := rootWeylLength_le (pairingC (n + 1)) (baseC n)
      (weylBCEquiv (n + 1) w) l (by
        change simpleReflectionWord (pairingB (n + 1)) (baseB n) l = w.val
        exact hl)
    exact hc.trans_eq hlen
  · obtain ⟨l, hlen, hl⟩ := rootWeylLength_spec (pairingC (n + 1)) (baseC n)
      (weylBCEquiv (n + 1) w)
    have hb := rootWeylLength_le (pairingB (n + 1)) (baseB n) w l (by
      change simpleReflectionWord (pairingC (n + 1)) (baseC n) l =
        (weylBCEquiv (n + 1) w).val
      exact hl)
    exact hb.trans_eq hlen

/-- Equality of the actual Weyl-length sums, not an assumed product formula. -/
theorem rootWeylPoincareEval_B_eq_C (n q : ℕ) :
    rootWeylPoincareEval (pairingB (n + 1)) (baseB n) q =
      rootWeylPoincareEval (pairingC (n + 1)) (baseC n) q := by
  letI : Fintype (pairingB (n + 1)).weylGroupToPerm.range := Fintype.ofFinite _
  letI : Fintype (pairingC (n + 1)).weylGroupToPerm.range := Fintype.ofFinite _
  change (∑ w : (pairingB (n + 1)).weylGroupToPerm.range,
    q ^ rootWeylLength (pairingB (n + 1)) (baseB n) w) =
      ∑ w : (pairingC (n + 1)).weylGroupToPerm.range,
        q ^ rootWeylLength (pairingC (n + 1)) (baseC n) w
  calc
    _ = ∑ w : (pairingB (n + 1)).weylGroupToPerm.range,
        q ^ rootWeylLength (pairingC (n + 1)) (baseC n) (weylBCEquiv (n + 1) w) := by
      simp only [weylBCEquiv_length]
    _ = _ := (weylBCEquiv (n + 1)).toEquiv.sum_comp
      (fun w => q ^ rootWeylLength (pairingC (n + 1)) (baseC n) w)

end Atlas.Chevalley.ClassicalData
