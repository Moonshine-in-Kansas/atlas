import Atlas.LinearGroups.Chevalley.Integral.MinusculeDCore
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDParity

/-! distinct D half-spin sign fibres inside the actual weight lattice.
Reflection stability/transitivity is not asserted by this first image/count unit. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

/-- Test a coordinate using the sum of two genuine D coroots. -/
def doubleCoordinate (n : ℕ) (i j : Fin (n+2)) (hij : i≠j) : CorootLattice (pairingD (n+2)) :=
  corootElement (pairingD (n+2)) (longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl)) +
  corootElement (pairingD (n+2)) (longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl))

theorem doubleCoordinate_apply (n : ℕ) (i j k : Fin (n+2)) (hij : i≠j) :
    (doubleCoordinate n i j hij).val (Pi.single k 1) = if k=i then 2 else 0 := by
  change coroot (longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl)) (Pi.single k 1) +
    coroot (longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) (Pi.single k 1) = _
  rw [coroot_long, coroot_long]
  by_cases hki : k=i
  · subst k
    simp [Pi.single_apply, hij, Ne.symm hij]
  · by_cases hkj : k=j
    · subst k
      simp [Pi.single_apply, hij, Ne.symm hij]
    · simp [Pi.single_apply, hki, hkj, Ne.symm hki, Ne.symm hkj]

theorem spinWeight_doubleCoordinate (n : ℕ) (σ : Fin (n+2) → Bool)
    (i j : Fin (n+2)) (hij : i≠j) : spinWeight n σ (doubleCoordinate n i j hij)=sign (σ i) := by
  have h := twice_spinWeight_apply n σ (doubleCoordinate n i j hij)
  simp only [doubleCoordinate_apply] at h
  simp [mul_ite] at h
  omega

/-- Actual half-spin weights retain their full sign-pattern information. -/
theorem spinWeight_injective (n : ℕ) : Function.Injective (spinWeight n) := by
  intro σ τ h
  funext i
  obtain ⟨j,hji⟩ := exists_ne i
  have he := congrArg (fun μ : WeightLattice (pairingD (n+2)) =>
    μ (doubleCoordinate n i j (Ne.symm hji))) h
  rw [spinWeight_doubleCoordinate, spinWeight_doubleCoordinate] at he
  cases hs : σ i <;> cases ht : τ i <;> first | rfl | (norm_num [sign, hs, ht] at he)

/-- The two labelled parity fibres remain separate finite sets of actual weights. -/
def halfSpinOrbit (n : ℕ) (ε : Bool) : Finset (WeightLattice (pairingD (n+2))) :=
  Finset.univ.image (fun σ : DParity.Fiber (n+2) ε => spinWeight n σ.val)

theorem halfSpinOrbit_card (n : ℕ) (ε : Bool) : (halfSpinOrbit n ε).card = 2^(n+1) := by
  have hi : Function.Injective (fun σ : DParity.Fiber (n+2) ε => spinWeight n σ.val) :=
    (spinWeight_injective n).comp Subtype.val_injective
  rw [halfSpinOrbit, Finset.card_image_of_injective _ hi]
  simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using DParity.fiber_card (n+1) ε

/-- Even and odd half-spin weights cannot accidentally collapse in the integral model. -/
theorem halfSpinOrbit_disjoint (n : ℕ) : Disjoint (halfSpinOrbit n true) (halfSpinOrbit n false) := by
  apply Finset.disjoint_left.mpr
  intro μ hμ hν
  obtain ⟨σ,_,hσ⟩ := Finset.mem_image.mp hμ
  obtain ⟨τ,_,hτ⟩ := Finset.mem_image.mp hν
  have he := spinWeight_injective n (hσ.trans hτ.symm)
  have hp := σ.property
  rw [he, τ.property] at hp
  norm_num [DParity.sign] at hp

end Atlas.Chevalley.Integral.Minuscule.TypeD
