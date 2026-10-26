import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Lemmas

/-! Local replacement for the global two-root-length step in
Geck's diamond proof. Only local pairings and invariant-form balance occur.
No IsIrreducible or IsNotG2 hypothesis. -/
noncomputable section
namespace Atlas.Chevalley.Integral
open RootPairing
variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]

/-- The local configuration reached in Geck Case 3 is impossible without
appealing to any theorem limiting the total number of root lengths. -/
theorem diamond_length_obstruction (i j k : ι)
    (hij : P.pairingIn ℤ i j = -1)
    (hkj : P.pairingIn ℤ k j = 2)
    (hki : P.pairingIn ℤ j i = P.pairingIn ℤ k i)
    (hne : P.root k ≠ P.root j) (hneg : P.root k ≠ -P.root j) : False := by
  have hp := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' k j hne hneg
  have hjk : P.pairingIn ℤ j k = 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
    omega
  letI : Fintype ι := Fintype.ofFinite ι
  let B : RootPositiveForm ℤ P := P.posRootForm ℤ
  have h₁ := B.pairingIn_mul_eq_pairingIn_mul_swap i j
  have h₂ := B.pairingIn_mul_eq_pairingIn_mul_swap k j
  have h₃ := B.pairingIn_mul_eq_pairingIn_mul_swap i k
  rw [hij, hki] at h₁
  rw [hjk, hkj, one_mul] at h₂
  rw [h₂] at h₃
  have hz : (2 * P.pairingIn ℤ i k + 1) * B.rootLength j = 0 := by
    nlinarith [h₁, h₃]
  have hodd : 2 * P.pairingIn ℤ i k + 1 = 0 :=
    (mul_eq_zero.mp hz).resolve_right (ne_of_gt (B.rootLength_pos j))
  omega

end Atlas.Chevalley.Integral
