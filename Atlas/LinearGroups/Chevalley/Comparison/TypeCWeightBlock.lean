import Atlas.LinearGroups.Chevalley.SelectedWeightCompanion
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! Literal coordinates of the existing selected type-C weight block.
No symplectic recognition, injectivity, or group order is used. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeC
open Classical ClassicalData Integral.Minuscule
open scoped Matrix

abbrev Index (r : ℕ) := Fin r ⊕ Fin r

def weightLabel (r : ℕ) : Index r → WeightOrbit (pairingC r) (Integral.Minuscule.TypeC.orbit r)
  | .inl k => ⟨Integral.Minuscule.TypeC.naturalWeight k 1,
      Integral.Minuscule.TypeC.naturalWeight_mem_orbit k 1 (Or.inl rfl)⟩
  | .inr k => ⟨Integral.Minuscule.TypeC.naturalWeight k (-1),
      Integral.Minuscule.TypeC.naturalWeight_mem_orbit k (-1) (Or.inr rfl)⟩

theorem weightLabel_injective (r : ℕ) : Function.Injective (weightLabel r) := by
  intro x y h
  have hi := Integral.Minuscule.TypeC.orbit_parameter_injective r
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hh : (i, true) = (j, true) := hi (congrArg Subtype.val h)
      exact congrArg Sum.inl (congrArg Prod.fst hh)
    | inr j =>
      have hh : (i, true) = (j, false) := hi (congrArg Subtype.val h)
      have := congrArg Prod.snd hh
      contradiction
  | inr i =>
    cases y with
    | inl j =>
      have hh : (i, false) = (j, true) := hi (congrArg Subtype.val h)
      have := congrArg Prod.snd hh
      contradiction
    | inr j =>
      have hh : (i, false) = (j, false) := hi (congrArg Subtype.val h)
      exact congrArg Sum.inr (congrArg Prod.fst hh)

theorem weightLabel_surjective (r : ℕ) : Function.Surjective (weightLabel r) := by
  intro μ
  obtain ⟨⟨k, s⟩, _, h⟩ := Finset.mem_image.mp μ.property
  cases s with
  | false => exact ⟨.inr k, Subtype.ext h⟩
  | true => exact ⟨.inl k, Subtype.ext h⟩

def indexEquiv (r : ℕ) :
    Index r ≃ WeightOrbit (pairingC r) (Integral.Minuscule.TypeC.orbit r) :=
  Equiv.ofBijective (weightLabel r) ⟨weightLabel_injective r, weightLabel_surjective r⟩

def reindex (r : ℕ) (R : Type*) [CommRing R] :
    Matrix (WeightOrbit (pairingC r) (Integral.Minuscule.TypeC.orbit r))
      (WeightOrbit (pairingC r) (Integral.Minuscule.TypeC.orbit r)) R ≃ₐ[R]
      Matrix (Index r) (Index r) R :=
  Matrix.reindexAlgEquiv R R (indexEquiv r).symm

def rawMatrixHom (n : ℕ) (hn : 2 ≤ n + 1) (R : Type*) [CommRing R] :
    SelectedWeightCompanion (.C (n + 1) hn) R →* Matrix (Index (n + 1)) (Index (n + 1)) R where
  toFun g := reindex (n + 1) R (g.val.2 ()).val
  map_one' := map_one (reindex (n + 1) R)
  map_mul' g h := map_mul (reindex (n + 1) R) (g.val.2 ()).val (h.val.2 ()).val

private theorem grade (r : ℕ) (a : BRoot r) (k : Index r) :
    (Integral.Minuscule.TypeC.actualStrings r).pairing a (weightLabel r k) =
      (weightLabel r k).val (corootElement (pairingC r) a) := rfl

private theorem grade_inl (r : ℕ) (a : BRoot r) (k : Fin r) :
    (Integral.Minuscule.TypeC.actualStrings r).pairing a (weightLabel r (.inl k)) =
      a.val k := by
  rw [grade]
  change (1 : ℤ) * a.val k = a.val k
  exact one_mul _

private theorem grade_inr (r : ℕ) (a : BRoot r) (k : Fin r) :
    (Integral.Minuscule.TypeC.actualStrings r).pairing a (weightLabel r (.inr k)) =
      -a.val k := by
  rw [grade]
  change (-1 : ℤ) * a.val k = -a.val k
  exact neg_one_mul _

private theorem reflect_pair (r : ℕ) (i j : Fin r) (hij : i ≠ j) (k : Index r) :
    (Integral.Minuscule.TypeC.actualStrings r).reflection
      (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) (weightLabel r k) =
      weightLabel r ((Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j)) k) := by
  cases k with
  | inl k =>
    apply Subtype.ext
    change weightReflection (pairingC r) _ (Integral.Minuscule.TypeC.naturalWeight k 1) = _
    rw [Integral.Minuscule.TypeC.reflection_long_label]
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [weightLabel, hi, hj, hij, Ne.symm hij, Equiv.swap_apply_def]
  | inr k =>
    apply Subtype.ext
    change weightReflection (pairingC r) _ (Integral.Minuscule.TypeC.naturalWeight k (-1)) = _
    rw [Integral.Minuscule.TypeC.reflection_long_label]
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [weightLabel, hi, hj, hij, Ne.symm hij, Equiv.swap_apply_def]

private theorem reflect_axis (r : ℕ) (i : Fin r) (k : Index r) :
    (Integral.Minuscule.TypeC.actualStrings r).reflection
      (shortRoot i 1 (Or.inl rfl)) (weightLabel r k) =
      weightLabel r (Equiv.swap (.inl i) (.inr i) k) := by
  cases k with
  | inl k =>
    apply Subtype.ext
    change weightReflection (pairingC r) _ (Integral.Minuscule.TypeC.naturalWeight k 1) = _
    rw [Integral.Minuscule.TypeC.reflection_short_label]
    by_cases hk : k = i <;> simp [weightLabel, hk, Equiv.swap_apply_def]
  | inr k =>
    apply Subtype.ext
    change weightReflection (pairingC r) _ (Integral.Minuscule.TypeC.naturalWeight k (-1)) = _
    rw [Integral.Minuscule.TypeC.reflection_short_label]
    by_cases hk : k = i <;> simp [weightLabel, hk, Equiv.swap_apply_def]

theorem raising_pair (r : ℕ) (R : Type*) [CommRing R] (i j : Fin r) (hij : i ≠ j) :
    reindex r R ((Integral.Minuscule.TypeC.actualStrings r).stepMatrix R
      (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) (-1)) =
      Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr j) (.inr i) 1 := by
  ext a b
  change (Integral.Minuscule.TypeC.actualStrings r).stepMatrix R _ (-1)
    (weightLabel r a) (weightLabel r b) = _
  cases b with
  | inl k =>
    rw [Strings.stepMatrix_entry, grade_inl, reflect_pair]
    simp only [(weightLabel_injective r).eq_iff]
    by_cases hki : k = i
    · subst k
      simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    by_cases hkj : k = j
    · subst k
      simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hki, Ne.symm hki, hkj, Ne.symm hkj, eq_comm]
  | inr k =>
    rw [Strings.stepMatrix_entry, grade_inr, reflect_pair]
    simp only [(weightLabel_injective r).eq_iff]
    by_cases hki : k = i
    · subst k
      simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    by_cases hkj : k = j
    · subst k
      simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hki, Ne.symm hki, hkj, Ne.symm hkj, eq_comm]

theorem lowering_pair (r : ℕ) (R : Type*) [CommRing R] (i j : Fin r) (hij : i ≠ j) :
    reindex r R ((Integral.Minuscule.TypeC.actualStrings r).stepMatrix R
      (longRoot true i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) 1) =
      Matrix.single (.inl j) (.inl i) 1 + Matrix.single (.inr i) (.inr j) 1 := by
  ext a b
  change (Integral.Minuscule.TypeC.actualStrings r).stepMatrix R _ 1
    (weightLabel r a) (weightLabel r b) = _
  cases b with
  | inl k =>
    rw [Strings.stepMatrix_entry, grade_inl, reflect_pair]
    simp only [(weightLabel_injective r).eq_iff]
    by_cases hki : k = i
    · subst k
      simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    by_cases hkj : k = j
    · subst k
      simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hki, Ne.symm hki, hkj, Ne.symm hkj, eq_comm]
  | inr k =>
    rw [Strings.stepMatrix_entry, grade_inr, reflect_pair]
    simp only [(weightLabel_injective r).eq_iff]
    by_cases hki : k = i
    · subst k
      simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    by_cases hkj : k = j
    · subst k
      simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    simp [longRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hki, Ne.symm hki, hkj, Ne.symm hkj, eq_comm]

theorem raising_axis (r : ℕ) (R : Type*) [CommRing R] (i : Fin r) :
    reindex r R ((Integral.Minuscule.TypeC.actualStrings r).stepMatrix R
      (shortRoot i 1 (Or.inl rfl)) (-1)) = Matrix.single (.inl i) (.inr i) 1 := by
  ext a b
  change (Integral.Minuscule.TypeC.actualStrings r).stepMatrix R _ (-1)
    (weightLabel r a) (weightLabel r b) = _
  cases b with
  | inl k =>
    rw [Strings.stepMatrix_entry, grade_inl, reflect_axis]
    simp only [(weightLabel_injective r).eq_iff]
    by_cases hki : k = i
    · subst k
      simp [shortRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, eq_comm]
    simp [shortRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hki, Ne.symm hki, eq_comm]
  | inr k =>
    rw [Strings.stepMatrix_entry, grade_inr, reflect_axis]
    simp only [(weightLabel_injective r).eq_iff]
    by_cases hki : k = i
    · subst k
      simp [shortRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, eq_comm]
    simp [shortRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hki, Ne.symm hki, eq_comm]

theorem lowering_axis (r : ℕ) (R : Type*) [CommRing R] (i : Fin r) :
    reindex r R ((Integral.Minuscule.TypeC.actualStrings r).stepMatrix R
      (shortRoot i 1 (Or.inl rfl)) 1) = Matrix.single (.inr i) (.inl i) 1 := by
  ext a b
  change (Integral.Minuscule.TypeC.actualStrings r).stepMatrix R _ 1
    (weightLabel r a) (weightLabel r b) = _
  cases b with
  | inl k =>
    rw [Strings.stepMatrix_entry, grade_inl, reflect_axis]
    simp only [(weightLabel_injective r).eq_iff]
    by_cases hki : k = i
    · subst k
      simp [shortRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, eq_comm]
    simp [shortRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hki, Ne.symm hki, eq_comm]
  | inr k =>
    rw [Strings.stepMatrix_entry, grade_inr, reflect_axis]
    simp only [(weightLabel_injective r).eq_iff]
    by_cases hki : k = i
    · subst k
      simp [shortRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, eq_comm]
    simp [shortRoot, Pi.single_apply, Matrix.single_apply, Equiv.swap_apply_def, hki, Ne.symm hki, eq_comm]

end Atlas.Chevalley.Comparison.TypeC
