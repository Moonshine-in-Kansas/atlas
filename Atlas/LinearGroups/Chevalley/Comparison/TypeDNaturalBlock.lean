import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionAdjoinOrbit
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDNatural
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! The descended natural D representation, on literal positive/negative coordinates,
with the exact two-entry matrices of its simple root generators. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeD
open Classical ClassicalData Integral.Minuscule
open scoped Matrix

abbrev Index (n : ℕ) := Fin (n+2) ⊕ Fin (n+2)

def weightLabel (n : ℕ) : Index n →
    WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2))
  | .inl i => ⟨Integral.Minuscule.TypeD.naturalWeight i 1,
      Integral.Minuscule.TypeD.naturalWeight_mem_naturalOrbit i 1 (Or.inl rfl)⟩
  | .inr i => ⟨Integral.Minuscule.TypeD.naturalWeight i (-1),
      Integral.Minuscule.TypeD.naturalWeight_mem_naturalOrbit i (-1) (Or.inr rfl)⟩

theorem weightLabel_injective (n : ℕ) : Function.Injective (weightLabel n) := by
  intro x y h
  have hi := Integral.Minuscule.TypeD.naturalOrbit_parameter_injective n
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hh : (i,true)=(j,true) := hi (congrArg Subtype.val h)
      exact congrArg Sum.inl (congrArg Prod.fst hh)
    | inr j =>
      have hh : (i,true)=(j,false) := hi (congrArg Subtype.val h)
      have := congrArg Prod.snd hh
      contradiction
  | inr i =>
    cases y with
    | inl j =>
      have hh : (i,false)=(j,true) := hi (congrArg Subtype.val h)
      have := congrArg Prod.snd hh
      contradiction
    | inr j =>
      have hh : (i,false)=(j,false) := hi (congrArg Subtype.val h)
      exact congrArg Sum.inr (congrArg Prod.fst hh)

theorem weightLabel_surjective (n : ℕ) : Function.Surjective (weightLabel n) := by
  intro μ
  obtain ⟨⟨i,s⟩,_,h⟩ := Finset.mem_image.mp μ.property
  cases s with
  | false => exact ⟨.inr i, Subtype.ext h⟩
  | true => exact ⟨.inl i, Subtype.ext h⟩

def indexEquiv (n : ℕ) : Index n ≃
    WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2)) :=
  Equiv.ofBijective (weightLabel n) ⟨weightLabel_injective n, weightLabel_surjective n⟩

def reindex (n : ℕ) (R : Type*) [CommRing R] :
    Matrix (WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2)))
      (WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2))) R ≃ₐ[R]
        Matrix (Index n) (Index n) R := Matrix.reindexAlgEquiv R R (indexEquiv n).symm

def naturalStrings (n : ℕ) : Strings (DRoot (n+2))
    (WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2))) :=
  stringsOfWeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2))
    Integral.Minuscule.TypeD.naturalOrbit_closed Integral.Minuscule.TypeD.naturalOrbit_minuscule

/-- A genuine unit-matrix representation of the selected half-spin companion. -/
def naturalRepresentation (n : ℕ) (hn : 4 ≤ n+2) (K : Type*) [Field K] :
    SelectedWeightCompanion (.D (n+2) hn) K →* (Matrix (Index n) (Index n) K)ˣ :=
  (Units.map (reindex n K).toMonoidHom).comp
    (selectedWeightCompanionOrbitRepresentation (.D (n+2) hn)
      (Integral.Minuscule.TypeD.naturalOrbit (n+2))
      Integral.Minuscule.TypeD.naturalOrbit_closed Integral.Minuscule.TypeD.naturalOrbit_minuscule K)

def rawMatrixHom (n : ℕ) (hn : 4 ≤ n+2) (K : Type*) [Field K] :
    SelectedWeightCompanion (.D (n+2) hn) K →* Matrix (Index n) (Index n) K :=
  (Units.coeHom _).comp (naturalRepresentation n hn K)

private theorem grade (n : ℕ) (a : DRoot (n+2)) (k : Index n) :
    (naturalStrings n).pairing a (weightLabel n k) =
      (match k with
        | .inl i => a.val i
        | .inr i => -a.val i) := by
  cases k with
  | inl i =>
    change Integral.Minuscule.TypeD.naturalWeight i 1
      (corootElement (pairingD (n+2)) a) = a.val i
    simpa only [one_mul] using Integral.Minuscule.TypeD.naturalWeight_pairing i 1 a
  | inr i =>
    change Integral.Minuscule.TypeD.naturalWeight i (-1)
      (corootElement (pairingD (n+2)) a) = -a.val i
    simpa only [neg_one_mul] using Integral.Minuscule.TypeD.naturalWeight_pairing i (-1) a

private theorem reflect_pair (n : ℕ) (i j : Fin (n+2)) (hij : i≠j) (k : Index n) :
    (naturalStrings n).reflection
      (longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) (weightLabel n k) =
      weightLabel n ((Equiv.sumCongr (Equiv.swap i j) (Equiv.swap i j)) k) := by
  cases k with
  | inl k =>
    apply Subtype.ext
    change weightReflection (pairingD (n+2)) _ (Integral.Minuscule.TypeD.naturalWeight k 1) = _
    rw [Integral.Minuscule.TypeD.naturalWeight_reflection_long]
    by_cases hi : k=i <;> by_cases hj : k=j <;>
      simp [weightLabel, hi, hj, hij, Ne.symm hij, Equiv.swap_apply_def]
  | inr k =>
    apply Subtype.ext
    change weightReflection (pairingD (n+2)) _ (Integral.Minuscule.TypeD.naturalWeight k (-1)) = _
    rw [Integral.Minuscule.TypeD.naturalWeight_reflection_long]
    by_cases hi : k=i <;> by_cases hj : k=j <;>
      simp [weightLabel, hi, hj, hij, Ne.symm hij, Equiv.swap_apply_def]

private def sumSwap (n : ℕ) (i j : Fin (n+2)) : Index n → Index n
  | .inl k => if k=i then .inr j else if k=j then .inr i else .inl k
  | .inr k => if k=i then .inl j else if k=j then .inl i else .inr k

private theorem reflect_sum (n : ℕ) (i j : Fin (n+2)) (hij : i≠j) (k : Index n) :
    (naturalStrings n).reflection
      (longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl)) (weightLabel n k) =
      weightLabel n (sumSwap n i j k) := by
  cases k with
  | inl k =>
    apply Subtype.ext
    change weightReflection (pairingD (n+2)) _ (Integral.Minuscule.TypeD.naturalWeight k 1) = _
    rw [Integral.Minuscule.TypeD.naturalWeight_reflection_long]
    by_cases hi : k=i <;> by_cases hj : k=j <;>
      simp [weightLabel, sumSwap, hi, hj, hij, Ne.symm hij]
  | inr k =>
    apply Subtype.ext
    change weightReflection (pairingD (n+2)) _ (Integral.Minuscule.TypeD.naturalWeight k (-1)) = _
    rw [Integral.Minuscule.TypeD.naturalWeight_reflection_long]
    by_cases hi : k=i <;> by_cases hj : k=j <;>
      simp [weightLabel, sumSwap, hi, hj, hij, Ne.symm hij]

theorem raising_pair (n : ℕ) (R : Type*) [CommRing R] (i j : Fin (n+2)) (hij : i≠j) :
    reindex n R ((naturalStrings n).stepMatrix R
      (longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) (-1)) =
      Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr j) (.inr i) 1 := by
  ext a b
  change (naturalStrings n).stepMatrix R _ (-1) (weightLabel n a) (weightLabel n b) = _
  rw [Strings.stepMatrix_entry, grade, reflect_pair]
  simp only [(weightLabel_injective n).eq_iff]
  cases a <;> cases b <;> rename_i a b
  all_goals
    simp only [longRoot, Pi.add_apply, Pi.single_apply]
  all_goals
    by_cases hbi : b = i
    · subst b
      simp [Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    · by_cases hbj : b = j
      · subst b
        simp [Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
      · simp [Matrix.single_apply, Equiv.swap_apply_def, hbi, hbj,
          Ne.symm hbi, Ne.symm hbj, hij, Ne.symm hij, eq_comm]

theorem lowering_pair (n : ℕ) (R : Type*) [CommRing R] (i j : Fin (n+2)) (hij : i≠j) :
    reindex n R ((naturalStrings n).stepMatrix R
      (longRoot false i j hij 1 (-1) (Or.inl rfl) (Or.inr rfl)) 1) =
      Matrix.single (.inl j) (.inl i) 1 + Matrix.single (.inr i) (.inr j) 1 := by
  ext a b
  change (naturalStrings n).stepMatrix R _ 1 (weightLabel n a) (weightLabel n b) = _
  rw [Strings.stepMatrix_entry, grade, reflect_pair]
  simp only [(weightLabel_injective n).eq_iff]
  cases a <;> cases b <;> rename_i a b
  all_goals
    simp only [longRoot, Pi.add_apply, Pi.single_apply]
  all_goals
    by_cases hbi : b = i
    · subst b
      simp [Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
    · by_cases hbj : b = j
      · subst b
        simp [Matrix.single_apply, Equiv.swap_apply_def, hij, Ne.symm hij, eq_comm]
      · simp [Matrix.single_apply, Equiv.swap_apply_def, hbi, hbj,
          Ne.symm hbi, Ne.symm hbj, hij, Ne.symm hij, eq_comm]

theorem raising_sum (n : ℕ) (R : Type*) [CommRing R] (i j : Fin (n+2)) (hij : i≠j) :
    reindex n R ((naturalStrings n).stepMatrix R
      (longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl)) (-1)) =
      Matrix.single (.inl i) (.inr j) 1 + Matrix.single (.inl j) (.inr i) 1 := by
  ext a b
  change (naturalStrings n).stepMatrix R _ (-1) (weightLabel n a) (weightLabel n b) = _
  rw [Strings.stepMatrix_entry, grade, reflect_sum]
  simp only [(weightLabel_injective n).eq_iff]
  cases a <;> cases b <;> rename_i a b
  all_goals
    simp only [longRoot, Pi.add_apply, Pi.single_apply]
  all_goals
    by_cases hbi : b = i
    · subst b
      simp [Matrix.single_apply, sumSwap, hij, Ne.symm hij, eq_comm]
    · by_cases hbj : b = j
      · subst b
        simp [Matrix.single_apply, sumSwap, hij, Ne.symm hij, eq_comm]
      · simp [Matrix.single_apply, sumSwap, hbi, hbj,
          Ne.symm hbi, Ne.symm hbj, hij, Ne.symm hij, eq_comm]

theorem lowering_sum (n : ℕ) (R : Type*) [CommRing R] (i j : Fin (n+2)) (hij : i≠j) :
    reindex n R ((naturalStrings n).stepMatrix R
      (longRoot false i j hij 1 1 (Or.inl rfl) (Or.inl rfl)) 1) =
      Matrix.single (.inr i) (.inl j) 1 + Matrix.single (.inr j) (.inl i) 1 := by
  ext a b
  change (naturalStrings n).stepMatrix R _ 1 (weightLabel n a) (weightLabel n b) = _
  rw [Strings.stepMatrix_entry, grade, reflect_sum]
  simp only [(weightLabel_injective n).eq_iff]
  cases a <;> cases b <;> rename_i a b
  all_goals
    simp only [longRoot, Pi.add_apply, Pi.single_apply]
  all_goals
    by_cases hbi : b = i
    · subst b
      simp [Matrix.single_apply, sumSwap, hij, Ne.symm hij, eq_comm]
    · by_cases hbj : b = j
      · subst b
        simp [Matrix.single_apply, sumSwap, hij, Ne.symm hij, eq_comm]
      · simp [Matrix.single_apply, sumSwap, hbi, hbj,
          Ne.symm hbi, Ne.symm hbj, hij, Ne.symm hij, eq_comm]

private theorem adjacent_ne {n : ℕ} (i : Fin (n+1)) : i.castSucc≠i.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc,Fin.val_succ] at hv
  omega

private theorem simple_pair (n : ℕ) (i : Fin (n+1)) :
    simpleD n i.castSucc = longRoot false i.castSucc i.succ (adjacent_ne i)
      1 (-1) (Or.inl rfl) (Or.inr rfl) := by
  have h : i.val≠n+1 := by omega
  simp only [simpleD, Fin.val_castSucc, h, dite_false]
  rfl

private theorem simple_sum (n : ℕ) :
    simpleD n (Fin.last (n+1)) =
      longRoot false (Fin.last n).castSucc (Fin.last n).succ (adjacent_ne (Fin.last n))
        1 1 (Or.inl rfl) (Or.inl rfl) := by
  simp only [simpleD, Fin.val_last, dite_true]
  rfl

theorem rawMatrix_X (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+2)) (t : K) :
    rawMatrixHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K i t) =
      reindex n K ((naturalStrings n).rootMatrix K (simpleD n i) (-1) t) := by
  classical
  letI : Fintype (WeightOrbit (rootDatum (.D (n+2) hn)).pairing
      (Integral.Minuscule.TypeD.naturalOrbit (n+2))) := by
    change Fintype {μ : WeightLattice (pairingD (n+2)) //
      μ ∈ Integral.Minuscule.TypeD.naturalOrbit (n+2)}
    infer_instance
  change reindex n K
    (selectedWeightCompanionOrbitRepresentation (.D (n+2) hn)
      (Integral.Minuscule.TypeD.naturalOrbit (n+2))
      Integral.Minuscule.TypeD.naturalOrbit_closed Integral.Minuscule.TypeD.naturalOrbit_minuscule K
      (selectedWeightCompanionX (.D (n+2) hn) K i t)).val = _
  exact congrArg (fun g :
      (Matrix (WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2)))
        (WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2))) K)ˣ =>
      reindex n K g.val)
    (selectedWeightCompanionOrbitRepresentation_X (.D (n+2) hn)
      (Integral.Minuscule.TypeD.naturalOrbit (n+2))
      Integral.Minuscule.TypeD.naturalOrbit_closed Integral.Minuscule.TypeD.naturalOrbit_minuscule
      K i t)

theorem rawMatrix_Y (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+2)) (t : K) :
    rawMatrixHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K i t) =
      reindex n K ((naturalStrings n).rootMatrix K (simpleD n i) 1 t) := by
  classical
  letI : Fintype (WeightOrbit (rootDatum (.D (n+2) hn)).pairing
      (Integral.Minuscule.TypeD.naturalOrbit (n+2))) := by
    change Fintype {μ : WeightLattice (pairingD (n+2)) //
      μ ∈ Integral.Minuscule.TypeD.naturalOrbit (n+2)}
    infer_instance
  change reindex n K
    (selectedWeightCompanionOrbitRepresentation (.D (n+2) hn)
      (Integral.Minuscule.TypeD.naturalOrbit (n+2))
      Integral.Minuscule.TypeD.naturalOrbit_closed Integral.Minuscule.TypeD.naturalOrbit_minuscule K
      (selectedWeightCompanionY (.D (n+2) hn) K i t)).val = _
  exact congrArg (fun g :
      (Matrix (WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2)))
        (WeightOrbit (pairingD (n+2)) (Integral.Minuscule.TypeD.naturalOrbit (n+2))) K)ˣ =>
      reindex n K g.val)
    (selectedWeightCompanionOrbitRepresentation_Y (.D (n+2) hn)
      (Integral.Minuscule.TypeD.naturalOrbit (n+2))
      Integral.Minuscule.TypeD.naturalOrbit_closed Integral.Minuscule.TypeD.naturalOrbit_minuscule
      K i t)

theorem matrix_X_pair (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+1)) (t : K) :
    rawMatrixHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K i.castSucc t) =
      1+t • (Matrix.single (.inl i.castSucc) (.inl i.succ) 1 +
        Matrix.single (.inr i.succ) (.inr i.castSucc) 1) := by
  rw [rawMatrix_X, Strings.rootMatrix, map_add, map_one, map_smul, simple_pair, raising_pair]

theorem matrix_Y_pair (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+1)) (t : K) :
    rawMatrixHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K i.castSucc t) =
      1+t • (Matrix.single (.inl i.succ) (.inl i.castSucc) 1 +
        Matrix.single (.inr i.castSucc) (.inr i.succ) 1) := by
  rw [rawMatrix_Y, Strings.rootMatrix, map_add, map_one, map_smul, simple_pair, lowering_pair]

theorem matrix_X_sum (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K] (t : K) :
    rawMatrixHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K (Fin.last (n+1)) t) =
      1+t • (Matrix.single (.inl (Fin.last n).castSucc) (.inr (Fin.last n).succ) 1 +
        Matrix.single (.inl (Fin.last n).succ) (.inr (Fin.last n).castSucc) 1) := by
  rw [rawMatrix_X, Strings.rootMatrix, map_add, map_one, map_smul, simple_sum, raising_sum]

theorem matrix_Y_sum (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K] (t : K) :
    rawMatrixHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K (Fin.last (n+1)) t) =
      1+t • (Matrix.single (.inr (Fin.last n).castSucc) (.inl (Fin.last n).succ) 1 +
        Matrix.single (.inr (Fin.last n).succ) (.inl (Fin.last n).castSucc) 1) := by
  rw [rawMatrix_Y, Strings.rootMatrix, map_add, map_one, map_smul, simple_sum, lowering_sum]

end Atlas.Chevalley.Comparison.TypeD
