import Atlas.LinearGroups.Chevalley.RootData.Classical
import Mathlib.Tactic

/-! Actual all-root pairing bounds, independent of irreducibility. -/
namespace Atlas.Chevalley.ClassicalData

/-- Every actual B/D coroot has value in [-2,2] on every actual root. -/
theorem coroot_root_bounds {n : ℕ} {allowShort : Bool} (a b : Root n allowShort) :
    -2 ≤ coroot b a.val ∧ coroot b a.val ≤ 2 := by
  rcases signed_support_classification b with ⟨hb,i,s,hs,hbval⟩ | ⟨i,j,hij,s,t,hs,ht,hbval⟩
  · subst allowShort
    have he : b=shortRoot i s hs := Subtype.ext hbval
    subst b
    rw [coroot_short]
    have hi := coordinate_bounds a i
    rcases hs with rfl | rfl <;> constructor <;> nlinarith
  · have he : b=longRoot allowShort i j hij s t hs ht := Subtype.ext hbval
    subst b
    rw [coroot_long]
    have hi := coordinate_bounds a i
    have hj := coordinate_bounds a j
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> constructor <;> nlinarith

theorem pairing_bounds (n : ℕ) (allowShort : Bool) (a b : Root n allowShort) :
    -2 ≤ (pairing n allowShort).pairing a b ∧ (pairing n allowShort).pairing a b ≤ 2 :=
  coroot_root_bounds a b

theorem pairingB_bounds (n : ℕ) (a b : BRoot n) :
    -2 ≤ (pairingB n).pairing a b ∧ (pairingB n).pairing a b ≤ 2 :=
  coroot_root_bounds a b

theorem pairingC_bounds (n : ℕ) (a b : BRoot n) :
    -2 ≤ (pairingC n).pairing a b ∧ (pairingC n).pairing a b ≤ 2 :=
  coroot_root_bounds b a

theorem pairingD_bounds (n : ℕ) (a b : DRoot n) :
    -2 ≤ (pairingD n).pairing a b ∧ (pairingD n).pairing a b ≤ 2 :=
  coroot_root_bounds a b

end Atlas.Chevalley.ClassicalData
