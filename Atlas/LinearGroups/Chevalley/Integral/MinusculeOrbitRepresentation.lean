import Atlas.LinearGroups.Chevalley.Integral.MinusculeStrings
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeightLattice

noncomputable section

namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]

/-- The coordinate labels are literal weights in the supplied finite subset. -/
abbrev WeightOrbit (S : Finset (WeightLattice P)) := {μ : WeightLattice P // μ ∈ S}

/-- Restriction of the existing integral reflection, with its inverse proved
by the existing integral involution theorem. -/
def weightOrbitReflection (S : Finset (WeightLattice P))
    (hclosed : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S) (i : ι) :
    Equiv.Perm (WeightOrbit P S) where
  toFun μ := ⟨weightReflection P i μ.val, hclosed i μ.val μ.property⟩
  invFun μ := ⟨weightReflection P i μ.val, hclosed i μ.val μ.property⟩
  left_inv μ := Subtype.ext (weightReflection_involutive P i μ.val)
  right_inv μ := Subtype.ext (weightReflection_involutive P i μ.val)

@[simp] theorem weightOrbitReflection_val (S : Finset (WeightLattice P))
    (hclosed : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
    (i : ι) (μ : WeightOrbit P S) :
    (weightOrbitReflection P S hclosed i μ).val = weightReflection P i μ.val := rfl

theorem weightOrbitReflection_involutive (S : Finset (WeightLattice P))
    (hclosed : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S) (i : ι) :
    Function.Involutive (weightOrbitReflection P S hclosed i) := by
  intro μ
  apply Subtype.ext
  exact weightReflection_involutive P i μ.val

/-- The minuscule range is checked on actual coroot evaluations of actual
weights. No rational ambient model or abstractly named target group is used. -/
def stringsOfWeightOrbit (S : Finset (WeightLattice P))
    (hclosed : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
    (hmin : ∀ μ ∈ S, ∀ i,
      μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
        μ (corootElement P i) = 1) : Strings ι (WeightOrbit P S) where
  pairing i μ := μ.val (corootElement P i)
  reflection := weightOrbitReflection P S hclosed
  involutive := weightOrbitReflection_involutive P S hclosed
  pairing_reflection i μ := weightReflection_grade P i μ.val
  minuscule i μ := hmin μ.val μ.property i

@[simp] theorem stringsOfWeightOrbit_pairing (S : Finset (WeightLattice P))
    (hclosed : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
    (hmin : ∀ μ ∈ S, ∀ i,
      μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
        μ (corootElement P i) = 1) (i : ι) (μ : WeightOrbit P S) :
    (stringsOfWeightOrbit P S hclosed hmin).pairing i μ =
      μ.val (corootElement P i) := rfl

@[simp] theorem stringsOfWeightOrbit_reflection (S : Finset (WeightLattice P))
    (hclosed : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
    (hmin : ∀ μ ∈ S, ∀ i,
      μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨
        μ (corootElement P i) = 1) (i : ι) (μ : WeightOrbit P S) :
    ((stringsOfWeightOrbit P S hclosed hmin).reflection i μ).val =
      weightReflection P i μ.val := rfl

end Atlas.Chevalley.Integral.Minuscule

namespace Atlas.Chevalley.Integral.Minuscule
open Classical
variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic]
  (S : Finset (WeightLattice P))
  (hclosed : ∀ i μ, μ ∈ S → weightReflection P i μ ∈ S)
  (hmin : ∀ μ ∈ S, ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

/-- Support and coefficient of the actual raising/lowering matrix on weights. -/
theorem weightOrbit_stepMatrix_entry (i : ι) (ε : ℤ) (μ ν : WeightOrbit P S) :
    (stringsOfWeightOrbit P S hclosed hmin).stepMatrix R i ε μ ν =
      if ν.val (corootElement P i) = ε ∧ weightReflection P i ν.val = μ.val then 1 else 0 := by
  rw [Strings.stepMatrix_entry]
  simp only [stringsOfWeightOrbit_pairing, Subtype.ext_iff, stringsOfWeightOrbit_reflection]

/-- An actual invertible matrix on the finite set of actual weights. -/
def weightOrbitRootElement (i : ι) (ε : ℤ) (hε : ε ≠ 0) (t : R) :
    (Matrix (WeightOrbit P S) (WeightOrbit P S) R)ˣ :=
  (stringsOfWeightOrbit P S hclosed hmin).rootMatrixUnit R i ε hε t

theorem weightOrbitRootElement_entry (i : ι) (ε : ℤ) (hε : ε ≠ 0) (t : R)
    (μ ν : WeightOrbit P S) :
    (weightOrbitRootElement P S hclosed hmin R i ε hε t).val μ ν =
      (if μ = ν then 1 else 0) +
        t * (if ν.val (corootElement P i) = ε ∧
          weightReflection P i ν.val = μ.val then 1 else 0) := by
  simp only [weightOrbitRootElement, Strings.rootMatrixUnit, Strings.rootMatrix,
    Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    weightOrbit_stepMatrix_entry]

end Atlas.Chevalley.Integral.Minuscule
