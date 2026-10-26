import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! The defining weight block of the new type-A companion, expressed on
literal coordinates. This supplies a marked matrix homomorphism; it does
not yet assert a comparison with SL or PSL. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeA
open Classical Integral.Minuscule Integral.Minuscule.TypeA TypeAData
open scoped Matrix

def weightLabel (r : ℕ) (j : Fin (r + 1)) :
    WeightOrbit (pairing (r + 1)) (naturalOrbit r) :=
  ⟨naturalWeight j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

theorem weightLabel_injective (r : ℕ) : Function.Injective (weightLabel r) := by
  intro i j h
  exact naturalWeight_injective (r + 1) (congrArg Subtype.val h)

theorem weightLabel_surjective (r : ℕ) : Function.Surjective (weightLabel r) := by
  intro μ
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp μ.property
  exact ⟨j, Subtype.ext hj⟩

def indexEquiv (r : ℕ) :
    Fin (r + 1) ≃ WeightOrbit (pairing (r + 1)) (naturalOrbit r) :=
  Equiv.ofBijective (weightLabel r)
    ⟨weightLabel_injective r, weightLabel_surjective r⟩

def reindex (r : ℕ) (R : Type*) [CommRing R] :
    Matrix (WeightOrbit (pairing (r + 1)) (naturalOrbit r))
      (WeightOrbit (pairing (r + 1)) (naturalOrbit r)) R ≃ₐ[R]
        Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.reindexAlgEquiv R R (indexEquiv r).symm

def weightMatrixHom (r : ℕ) (hr : 1 ≤ r) (R : Type*) [CommRing R] :
    SelectedWeightCompanion (.A r hr) R →* Matrix (Fin (r + 1)) (Fin (r + 1)) R where
  toFun g := reindex r R (g.val.2 ()).val
  map_one' := map_one (reindex r R)
  map_mul' g h := map_mul (reindex r R) (g.val.2 ()).val (h.val.2 ()).val

theorem actualStrings_grade (r : ℕ) (a : Root (r + 1)) (j : Fin (r + 1)) :
    (actualStrings r).pairing a (weightLabel r j) =
      naturalWeight j (corootElement (pairing (r + 1)) a) := rfl

theorem actualStrings_reflection (r : ℕ) (a : Root (r + 1)) (j : Fin (r + 1)) :
    (actualStrings r).reflection a (weightLabel r j) =
      weightLabel r (Equiv.swap a.val.1 a.val.2 j) :=
  Subtype.ext (naturalWeight_reflection a j)

theorem raising_step (r : ℕ) (R : Type*) [CommRing R] (a : Root (r + 1)) :
    reindex r R ((actualStrings r).stepMatrix R a (-1)) =
      Matrix.single a.val.1 a.val.2 1 := by
  ext i j
  change (actualStrings r).stepMatrix R a (-1) (weightLabel r i) (weightLabel r j) = _
  rw [Strings.stepMatrix_entry, actualStrings_grade, actualStrings_reflection]
  simp only [(weightLabel_injective r).eq_iff]
  rw [naturalWeight_pairing]
  by_cases hj : j = a.val.2
  · subst j
    simp [a.property, Matrix.single_apply, eq_comm]
  · by_cases hj' : j = a.val.1
    · subst j
      simp [a.property, Matrix.single_apply, eq_comm]
    · simp [hj, hj', Ne.symm hj, Ne.symm hj', Matrix.single_apply]

theorem lowering_step (r : ℕ) (R : Type*) [CommRing R] (a : Root (r + 1)) :
    reindex r R ((actualStrings r).stepMatrix R a 1) =
      Matrix.single a.val.2 a.val.1 1 := by
  ext i j
  change (actualStrings r).stepMatrix R a 1 (weightLabel r i) (weightLabel r j) = _
  rw [Strings.stepMatrix_entry, actualStrings_grade, actualStrings_reflection]
  simp only [(weightLabel_injective r).eq_iff]
  rw [naturalWeight_pairing]
  by_cases hj : j = a.val.1
  · subst j
    simp [a.property, Matrix.single_apply, eq_comm]
  · by_cases hj' : j = a.val.2
    · subst j
      simp [a.property, Matrix.single_apply, eq_comm]
    · simp [hj, hj', Ne.symm hj, Ne.symm hj', Matrix.single_apply]

theorem matrix_X (r : ℕ) (hr : 1 ≤ r) (R : Type*) [CommRing R]
    (i : Fin r) (t : R) :
    weightMatrixHom r hr R (selectedWeightCompanionX (.A r hr) R i t) =
      Matrix.transvection i.castSucc i.succ t := by
  change reindex r R ((actualStrings r).rootMatrix R (simpleRoot i) (-1) t) = _
  rw [Strings.rootMatrix, map_add, map_one, map_smul, raising_step]
  simp [Matrix.transvection, simpleRoot, Matrix.smul_single, smul_eq_mul]

theorem matrix_Y (r : ℕ) (hr : 1 ≤ r) (R : Type*) [CommRing R]
    (i : Fin r) (t : R) :
    weightMatrixHom r hr R (selectedWeightCompanionY (.A r hr) R i t) =
      Matrix.transvection i.succ i.castSucc t := by
  change reindex r R ((actualStrings r).rootMatrix R (simpleRoot i) 1 t) = _
  rw [Strings.rootMatrix, map_add, map_one, map_smul, lowering_step]
  simp [Matrix.transvection, simpleRoot, Matrix.smul_single, smul_eq_mul]

end Atlas.Chevalley.Comparison.TypeA
