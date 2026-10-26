import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2Correspondence
import Atlas.LinearGroups.Chevalley.Integral.GeckExponential
import Mathlib.LinearAlgebra.Matrix.Reindex
/-! Actual C2 exponential correspondence. Integral divided powers precede arbitrary commutative-ring base change. -/
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData Integral C2IntegerTemplate
open scoped Matrix

noncomputable section
local instance c2ExponentialRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance c2ExponentialBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The opposition involution is the actual root-negation permutation. -/
theorem c2_opposition_entry (i j : Fin 10) :
    (RootPairing.GeckConstruction.ω (baseC 1) :
      Matrix ((baseC 1).support ⊕ BRoot 2) ((baseC 1).support ⊕ BRoot 2) ℤ)
      (c2IndexEquiv i) (c2IndexEquiv j) = omega i j := by
  have hn (k : Fin 8) :
      (pairingC (1+1)).reflectionPerm (label k) (label k) =
        label (oppositeLabel k) := c_reflection_self_label k
  fin_cases i <;> fin_cases j <;>
    norm_num [c2IndexEquiv, c2_sum_split, labelEquiv_apply,
      RootPairing.GeckConstruction.ω, c_neg_label, c_reflection_self_label,
      label_injective.eq_iff, oppositeLabel, omega, Matrix.fromBlocks, hn] <;> decide

/-- Reindex actual powers before taking the justified integral quotient. -/
theorem c2_divided_entry (k : Fin 2) (n : ℕ) (i j : Fin 10) :
    raisingDividedPower (pairingC 2) (baseC 1) (baseCIndexEquiv 1 k) n
      (c2IndexEquiv i) (c2IndexEquiv j) =
      (c2ActualRaising k ^ n) i j / (n.factorial : ℤ) := by
  let E := Matrix.reindexAlgEquiv ℤ ℤ c2IndexEquiv.symm
  have hE : E (raising (pairingC 2) (baseC 1) (baseCIndexEquiv 1 k)) =
      c2ActualRaising k := rfl
  have hp := E.map_pow (raising (pairingC 2) (baseC 1) (baseCIndexEquiv 1 k)) n
  change E (raising (pairingC 2) (baseC 1) (baseCIndexEquiv 1 k) ^ n) =
    E (raising (pairingC 2) (baseC 1) (baseCIndexEquiv 1 k)) ^ n at hp
  rw [hE] at hp
  have he := congrArg (fun A => A i j) hp
  change (raising (pairingC 2) (baseC 1) (baseCIndexEquiv 1 k) ^ n)
      (c2IndexEquiv i) (c2IndexEquiv j) = (c2ActualRaising k ^ n) i j at he
  unfold raisingDividedPower
  exact congrArg (fun z : ℤ => z / (n.factorial : ℤ)) he

/-- Integral quotients are computed before any base change, including to F3. -/
theorem ea_divided_coefficients (n : Fin 4) (i j : Fin 10) :
    ((ea : Matrix (Fin 10) (Fin 10) ℤ) ^ n.val) i j / (n.val.factorial : ℤ) =
      (![1, ea, ea2, 0] n) i j := by
  fin_cases n <;> fin_cases i <;> fin_cases j <;> decide

theorem eb_divided_coefficients (n : Fin 4) (i j : Fin 10) :
    ((eb : Matrix (Fin 10) (Fin 10) ℤ) ^ n.val) i j / (n.val.factorial : ℤ) =
      (![1, eb, eb2, 0] n) i j := by
  fin_cases n <;> fin_cases i <;> fin_cases j <;> decide

variable {R : Type*} [CommRing R]

def xaOver (t : R) : Matrix (Fin 10) (Fin 10) R :=
  1 + t • ea.map (Int.castRingHom R) + t^2 • ea2.map (Int.castRingHom R)

def xbOver (t : R) : Matrix (Fin 10) (Fin 10) R :=
  1 + t • eb.map (Int.castRingHom R) + t^2 • eb2.map (Int.castRingHom R)

set_option simprocs false in
/-- The target ring never divides by2 or3: these are the actual Geck exponentials. -/
theorem c2_exponential_short (t : R) (i j : Fin 10) :
    raisingExponential (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) t
      (c2IndexEquiv i) (c2IndexEquiv j) = xaOver t i j := by
  simp only [raisingExponential_expansion, raisingDividedOver, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, c2_divided_entry,
    c2ActualRaising_zero]
  erw [ea_divided_coefficients (0 : Fin 4), ea_divided_coefficients (1 : Fin 4),
    ea_divided_coefficients (2 : Fin 4), ea_divided_coefficients (3 : Fin 4)]
  rw [show (![1, ea, ea2, 0] : Fin 4 → Matrix (Fin 10) (Fin 10) ℤ) 2 = ea2 from rfl,
    show (![1, ea, ea2, 0] : Fin 4 → Matrix (Fin 10) (Fin 10) ℤ) 3 = 0 from rfl]
  simp [xaOver, Matrix.map_apply, Matrix.one_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

set_option simprocs false in
theorem c2_exponential_long (t : R) (i j : Fin 10) :
    raisingExponential (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) t
      (c2IndexEquiv i) (c2IndexEquiv j) = xbOver t i j := by
  simp only [raisingExponential_expansion, raisingDividedOver, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, c2_divided_entry,
    c2ActualRaising_one]
  erw [eb_divided_coefficients (0 : Fin 4), eb_divided_coefficients (1 : Fin 4),
    eb_divided_coefficients (2 : Fin 4), eb_divided_coefficients (3 : Fin 4)]
  rw [show (![1, eb, eb2, 0] : Fin 4 → Matrix (Fin 10) (Fin 10) ℤ) 2 = eb2 from rfl,
    show (![1, eb, eb2, 0] : Fin 4 → Matrix (Fin 10) (Fin 10) ℤ) 3 = 0 from rfl]
  simp [xbOver, Matrix.map_apply, Matrix.one_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

end
end Atlas.Chevalley.Integral.RankTwo
