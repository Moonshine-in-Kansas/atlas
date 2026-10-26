import Atlas.LinearGroups.Chevalley.Integral.LocalDiamondCommutation

/-! Simply-laced local root-string diamonds. No integer irreducibility or IsNotG2 instance.
The argument uses finite crystallographic reduced root-string theory only. -/
noncomputable section
namespace Atlas.Chevalley.Integral
open Set
variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
    (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]

/-- A nonvacuous simply-laced arithmetic condition: independent root pairs
have pairing at most one. Ordered quantification covers both directions. -/
def IndependentPairingBound : Prop :=
  ∀ i j : ι, LinearIndependent ℤ ![P.root i, P.root j] → P.pairingIn ℤ j i ≤ 1

/-- Symmetric root/coroot pairings suffice, using mathlib's finite pair list.
No invariant-submodule irreducibility assumption is used by that list. -/
theorem independentPairingBound_of_symmetric
    (hsym : ∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i) :
    IndependentPairingBound P := by
  intro i j hij
  have hn := (RootPairing.IsReduced.linearIndependent_iff P).mp hij
  have hpair := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i j
    (fun h => hn.1 (P.root.injective h)) hn.2
  have hs := hsym i j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hpair
  omega

/-- All nontrivial strings have length at most one under the explicit bound. -/
theorem chain_length_le_one (hb : IndependentPairingBound P) (i j : ι) :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 1 := by
  by_cases h : LinearIndependent ℤ ![P.root i, P.root j]
  · have ht : LinearIndependent ℤ ![P.root i, P.root (P.chainTopIdx i j)] := by
      rwa [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
        LinearIndependent.pair_add_smul_right_iff]
    have hp := hb i (P.chainTopIdx i j) ht
    have he := P.chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h
    omega
  · simp [P.chainTopCoeff_of_not_linearIndependent h,
      P.chainBotCoeff_of_not_linearIndependent h]

/-- A forward root step leaves no backward step in a length-one string. -/
theorem chain_bot_zero_of_add (hb : IndependentPairingBound P) (i j : ι)
    (h : P.root i + P.root j ∈ Set.range P.root) : P.chainBotCoeff i j = 0 := by
  have ht := P.one_le_chainTopCoeff_of_root_add_mem h
  have hlen := chain_length_le_one P hb i j
  omega

/-- The analogous backward-root-step statement. -/
theorem chain_top_zero_of_sub (hb : IndependentPairingBound P) (i j : ι)
    (h : P.root j - P.root i ∈ Set.range P.root) : P.chainTopCoeff i j = 0 := by
  have h' : P.root i - P.root j ∈ Set.range P.root := by
    rwa [← P.neg_mem_range_root_iff, neg_sub]
  have ht := P.one_le_chainBotCoeff_of_root_add_mem h'
  have hlen := chain_length_le_one P hb i j
  omega

/-- In every simply-laced diamond, all four Geck factors are one. -/
theorem simpleDiamondProducts_of_independentPairingBound
    (hb : IndependentPairingBound P) (b : P.Base) : SimpleDiamondProducts P b := by
  intro i j _ k l m hplus hminus hdiamond
  have him : P.root i + P.root m ∈ Set.range P.root := by
    rw [← hminus]
    have he : P.root i + (P.root k - P.root j) =
        P.root k + P.root i - P.root j := by abel
    rw [he]
    exact hdiamond
  have hik : P.root i + P.root k ∈ Set.range P.root :=
    ⟨l, by rw [← hplus, add_comm]⟩
  have hjk : P.root k - P.root j ∈ Set.range P.root := ⟨m, hminus.symm⟩
  have hjl : P.root l - P.root j ∈ Set.range P.root := by rwa [← hplus]
  rw [chain_bot_zero_of_add P hb i m him, chain_top_zero_of_sub P hb j k hjk,
    chain_top_zero_of_sub P hb j l hjl, chain_bot_zero_of_add P hb i k hik]

/-- Applicable to actual simply-laced data once their symmetric pairing is
proved from their displayed forms; no all-type finite enumeration is needed. -/
theorem simpleDiamondProducts_of_symmetric
    (hsym : ∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i) (b : P.Base) :
    SimpleDiamondProducts P b :=
  simpleDiamondProducts_of_independentPairingBound P
    (independentPairingBound_of_symmetric P hsym) b

end Atlas.Chevalley.Integral
