import Atlas.LinearGroups.ReeF4.TorusWeights
import Atlas.LinearGroups.ReeF4.StarRootTargets

/-! The finite root-character identity underlying torus/star compatibility.
The only twist assumption in the group-theoretic lemma is τ²(a)=a² and
τ²(b)=b². Its finite-field instantiation belongs downstream. -/
namespace Atlas.ReeF4

def torusConstantExponents (r : ShortRootLabel) : ℤ × ℤ :=
  (![![(1,0), (-1,0), (-1,0), (1,2), (-1,-2), (1,0), (1,0), (-1,0)],
     ![(-1,-1), (1,1), (1,1), (1,-1), (-1,1), (-1,-1), (-1,-1), (1,1)],
     ![(0,1), (0,-1), (0,-1), (-2,-1), (2,1), (0,1), (0,1), (0,-1)]]) r.1 r.2

def torusThetaExponents (r : ShortRootLabel) : ℤ × ℤ :=
  (![![(0,0), (1,0), (0,1), (-1,-1), (1,1), (0,-1), (-1,0), (0,0)],
     ![(1,1), (0,-1), (-1,0), (0,0), (0,0), (1,0), (0,1), (-1,-1)],
     ![(0,0), (1,0), (0,1), (1,1), (-1,-1), (0,-1), (-1,0), (0,0)]]) r.1 r.2

theorem torusWeightExponents_decompose (m : ℕ) (r : ShortRootLabel) :
    torusWeightExponents m r = torusConstantExponents r +
      (2^(m+1) : ℕ) • torusThetaExponents r := by
  rcases r with ⟨b,j⟩
  fin_cases b <;> fin_cases j <;> ext <;>
    simp [torusWeightExponents, torusConstantExponents, torusThetaExponents,
      nsmul_eq_mul] <;> ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- A finite root-label check, independent of a field or group representation.
theorem torusStar_exponents : ∀ r s : ShortRootLabel,
    rootDot (scaledShortRoot r) (scaledShortRoot s) = 0 →
      torusConstantExponents r + torusConstantExponents s =
        torusThetaExponents (starRootTarget r s) + torusThetaExponents (starRootTarget r s) ∧
      torusThetaExponents r + torusThetaExponents s =
        torusConstantExponents (starRootTarget r s) := by decide

variable {G : Type*} [CommGroup G]

def torusCharacter (a b : G) (e : ℤ × ℤ) : G := a ^ e.1 * b ^ e.2

theorem torusCharacter_add (a b : G) (e f : ℤ × ℤ) :
    torusCharacter a b (e+f) = torusCharacter a b e * torusCharacter a b f := by
  simp only [torusCharacter, Prod.fst_add, Prod.snd_add, zpow_add]
  ac_rfl

theorem torusCharacter_mul (a b c d : G) (e : ℤ × ℤ) :
    torusCharacter (a*c) (b*d) e = torusCharacter a b e * torusCharacter c d e := by
  simp only [torusCharacter, mul_zpow]
  ac_rfl

theorem torusCharacter_map (τ : G →* G) (a b : G) (e : ℤ × ℤ) :
    τ (torusCharacter a b e) = torusCharacter (τ a) (τ b) e := by
  simp [torusCharacter]

theorem torusCharacter_nsmul (a b : G) (n : ℕ) (e : ℤ × ℤ) :
    torusCharacter a b (n • e) = torusCharacter (a^n) (b^n) e := by
  change a ^ ((n : ℤ) * e.1) * b ^ ((n : ℤ) * e.2) = _
  rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rfl

def twistedTorusWeight
 (τ : G →* G) (a b : G) (r : ShortRootLabel) : G :=
  torusCharacter a b (torusConstantExponents r) *
    torusCharacter (τ a) (τ b) (torusThetaExponents r)

theorem torusWeight_eq_twisted (m : ℕ) (τ : G →* G) (a b : G)
    (ha : τ a = a ^ (2^(m+1))) (hb : τ b = b ^ (2^(m+1))) (r : ShortRootLabel) :
    torusWeight m a b r = twistedTorusWeight τ a b r := by
  change torusCharacter a b (torusWeightExponents m r) = _
  rw [torusWeightExponents_decompose, torusCharacter_add, torusCharacter_nsmul,
    ← ha, ← hb]
  rfl

theorem twistedTorusWeight_star
 (τ : G →* G) (a b : G)
    (ha : τ (τ a) = a^2) (hb : τ (τ b) = b^2) (r s : ShortRootLabel)
    (hp : rootDot (scaledShortRoot r) (scaledShortRoot s) = 0) :
    twistedTorusWeight τ a b r * twistedTorusWeight τ a b s =
      τ (twistedTorusWeight τ a b (starRootTarget r s)) := by
  obtain ⟨hc, ht⟩ := torusStar_exponents r s hp
  calc
    _ = torusCharacter a b (torusConstantExponents r + torusConstantExponents s) *
        torusCharacter (τ a) (τ b) (torusThetaExponents r + torusThetaExponents s) := by
      simp only [twistedTorusWeight, torusCharacter_add]
      ac_rfl
    _ = _ := by
      rw [hc, ht, torusCharacter_add]
      simp only [twistedTorusWeight, map_mul, torusCharacter_map, ha, hb,
        pow_two, torusCharacter_mul]
      ac_rfl

end Atlas.ReeF4
