import Atlas.LinearGroups.Chevalley.Integral.MinusculeABCRepresentations
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Literal Boolean coordinates of the existing integral type-B spin strings.
The final simple short-root operators have coefficient +1, in every characteristic.
No Clifford faithfulness, target group identification or group order is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeB
open Classical ClassicalData Integral.Minuscule
open scoped Matrix

abbrev SpinIndex (n : ℕ) := Fin (n+1) → Bool

def spinLabel (n : ℕ) (σ : SpinIndex n) :
    WeightOrbit (pairingB (n+1)) (Integral.Minuscule.TypeB.spinOrbit n) :=
  ⟨Integral.Minuscule.TypeB.spinWeight n σ,
    Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩⟩

theorem spinLabel_injective (n : ℕ) : Function.Injective (spinLabel n) := by
  intro σ τ h
  apply Integral.Minuscule.TypeB.spinWeight_injective n
  exact congrArg (fun μ : WeightOrbit (pairingB (n+1))
    (Integral.Minuscule.TypeB.spinOrbit n) => μ.val) h

theorem spinLabel_surjective (n : ℕ) : Function.Surjective (spinLabel n) := by
  intro μ
  obtain ⟨σ, _, h⟩ := Finset.mem_image.mp μ.property
  exact ⟨σ, Subtype.ext h⟩

def spinIndexEquiv (n : ℕ) :
    SpinIndex n ≃ WeightOrbit (pairingB (n+1)) (Integral.Minuscule.TypeB.spinOrbit n) :=
  Equiv.ofBijective (spinLabel n) ⟨spinLabel_injective n, spinLabel_surjective n⟩

def spinReindex (n : ℕ) (R : Type*) [CommRing R] :
    Matrix (WeightOrbit (pairingB (n+1)) (Integral.Minuscule.TypeB.spinOrbit n))
      (WeightOrbit (pairingB (n+1)) (Integral.Minuscule.TypeB.spinOrbit n)) R ≃ₐ[R]
      Matrix (SpinIndex n) (SpinIndex n) R :=
  Matrix.reindexAlgEquiv R R (spinIndexEquiv n).symm

private theorem short_grade (n : ℕ) (i : Fin (n+1)) (σ : SpinIndex n) :
    (Integral.Minuscule.TypeB.actualStrings n).pairing
      (shortRoot i 1 (Or.inl rfl)) (spinLabel n σ) = Integral.Minuscule.TypeB.sign (σ i) := by
  change Integral.Minuscule.TypeB.spinWeight n σ
    (corootElement (pairingB (n+1)) (shortRoot i 1 (Or.inl rfl))) = _
  rw [Integral.Minuscule.TypeB.spinWeight_short_pairing, one_mul]

private theorem short_reflection (n : ℕ) (i : Fin (n+1)) (σ : SpinIndex n) :
    (Integral.Minuscule.TypeB.actualStrings n).reflection
      (shortRoot i 1 (Or.inl rfl)) (spinLabel n σ) =
      spinLabel n (Function.update σ i (!(σ i))) := by
  apply Subtype.ext
  change weightReflection (pairingB (n+1)) _ (Integral.Minuscule.TypeB.spinWeight n σ) = _
  rw [Integral.Minuscule.TypeB.spinWeight_reflection,
    Integral.Minuscule.TypeB.short_reflectedSigns]
  rfl

theorem spin_raising_short (n : ℕ) (R : Type*) [CommRing R] (i : Fin (n+1)) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (shortRoot i 1 (Or.inl rfl)) (-1)) =
      fun σ τ => if τ i = false ∧ Function.update τ i true = σ then 1 else 0 := by
  ext σ τ
  change (Integral.Minuscule.TypeB.actualStrings n).stepMatrix R _ (-1)
    (spinLabel n σ) (spinLabel n τ) = _
  rw [Strings.stepMatrix_entry, short_grade, short_reflection]
  simp only [(spinLabel_injective n).eq_iff]
  cases h : τ i <;> simp [Integral.Minuscule.TypeB.sign, h]

theorem spin_lowering_short (n : ℕ) (R : Type*) [CommRing R] (i : Fin (n+1)) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).stepMatrix R
      (shortRoot i 1 (Or.inl rfl)) 1) =
      fun σ τ => if τ i = true ∧ Function.update τ i false = σ then 1 else 0 := by
  ext σ τ
  change (Integral.Minuscule.TypeB.actualStrings n).stepMatrix R _ 1
    (spinLabel n σ) (spinLabel n τ) = _
  rw [Strings.stepMatrix_entry, short_grade, short_reflection]
  simp only [(spinLabel_injective n).eq_iff]
  cases h : τ i <;> simp [Integral.Minuscule.TypeB.sign, h]

theorem spin_X_short_entry (n : ℕ) (R : Type*) [CommRing R] (i : Fin (n+1))
    (t : R) (σ τ : SpinIndex n) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (shortRoot i 1 (Or.inl rfl)) (-1) t) σ τ =
      (if σ = τ then 1 else 0) +
        t * (if τ i = false ∧ Function.update τ i true = σ then 1 else 0) := by
  have h := congrArg (fun A : Matrix (SpinIndex n) (SpinIndex n) R => A σ τ)
    (spin_raising_short n R i)
  change (Integral.Minuscule.TypeB.actualStrings n).stepMatrix R _ (-1)
    (spinLabel n σ) (spinLabel n τ) = _ at h
  change (Integral.Minuscule.TypeB.actualStrings n).rootMatrix R _ (-1) t
    (spinLabel n σ) (spinLabel n τ) = _
  simp only [Strings.rootMatrix, Matrix.add_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, (spinLabel_injective n).eq_iff, h]

theorem spin_Y_short_entry (n : ℕ) (R : Type*) [CommRing R] (i : Fin (n+1))
    (t : R) (σ τ : SpinIndex n) :
    spinReindex n R ((Integral.Minuscule.TypeB.actualStrings n).rootMatrix R
      (shortRoot i 1 (Or.inl rfl)) 1 t) σ τ =
      (if σ = τ then 1 else 0) +
        t * (if τ i = true ∧ Function.update τ i false = σ then 1 else 0) := by
  have h := congrArg (fun A : Matrix (SpinIndex n) (SpinIndex n) R => A σ τ)
    (spin_lowering_short n R i)
  change (Integral.Minuscule.TypeB.actualStrings n).stepMatrix R _ 1
    (spinLabel n σ) (spinLabel n τ) = _ at h
  change (Integral.Minuscule.TypeB.actualStrings n).rootMatrix R _ 1 t
    (spinLabel n σ) (spinLabel n τ) = _
  simp only [Strings.rootMatrix, Matrix.add_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, (spinLabel_injective n).eq_iff, h]

end Atlas.Chevalley.Comparison.TypeB
