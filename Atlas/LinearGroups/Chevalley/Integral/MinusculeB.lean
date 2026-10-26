import Atlas.LinearGroups.Chevalley.RootData.ClassicalBasesBC
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeightLattice
import Mathlib.Tactic
import Mathlib.Logic.Relation

/-! Type-B spin weights in the actual integral coroot dual.
The sign pattern is a finite type; no spin vector is silently placed in Z^r. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeB
open Classical ClassicalData

def sign (b : Bool) : ℤ := if b then 1 else -1

/-- Consecutive sign differences divided integrally by two, by explicit cases. -/
def halfDifference (a b : Bool) : ℤ :=
  if a then (if b then 0 else 1) else (if b then -1 else 0)

theorem twice_halfDifference (a b : Bool) :
    2 * halfDifference a b = sign a - sign b := by
  cases a <;> cases b <;> decide

/-- Fundamental-weight coordinates with the checked final-short B node convention. -/
def spinCoordinates (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin (n+1)) : ℤ :=
  if h : i.val < n then halfDifference (σ i) (σ ⟨i.val+1, by omega⟩)
  else sign (σ i)

/-- An actual functional on Q∨, obtained from its integral simple-coroot values. -/
def spinWeight (n : ℕ) (σ : Fin (n+1) → Bool) : WeightLattice (pairingB (n+1)) :=
  (weightCoordinates (pairingB (n+1)) (baseB n)).symm
    (fun j => spinCoordinates n σ ((baseBIndexEquiv n).symm j))

/-- Its coordinate formula is certified by the actual dual-basis equivalence. -/
theorem spinWeight_coordinates (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin (n+1)) :
    weightCoordinates (pairingB (n+1)) (baseB n) (spinWeight n σ)
      (baseBIndexEquiv n i) = spinCoordinates n σ i := by
  simp only [spinWeight, LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The unique all-positive pattern has final fundamental coordinate 1. -/
theorem positive_spinCoordinates (n : ℕ) (i : Fin (n+1)) :
    spinCoordinates n (fun _ => true) i = if i = Fin.last n then 1 else 0 := by
  simp only [spinCoordinates, halfDifference, Bool.true_eq, ↓reduceIte, sign]
  by_cases hi : i.val < n
  · have hn : i ≠ Fin.last n := by intro h; subst i; simp at hi
    simp [hi, hn]
  · have hn : i = Fin.last n := Fin.ext (by change i.val=n; have := i.isLt; omega)
    simp [hi, hn]

/-- The selected B spin weight is the last fundamental weight of the actual base. -/
theorem positive_spinWeight (n : ℕ) :
    spinWeight n (fun _ => true) =
      fundamentalWeights (pairingB (n+1)) (baseB n) (baseBIndexEquiv n (Fin.last n)) := by
  apply (weightCoordinates (pairingB (n+1)) (baseB n)).injective
  funext j
  obtain ⟨i, rfl⟩ := (baseBIndexEquiv n).surjective j
  rw [spinWeight_coordinates, positive_spinCoordinates, weightCoordinates_apply,
    fundamentalWeights_pairing]
  simp

/-- Signed evaluation on the ambient dual, restricted to Q∨.
The forthcoming identity `2 • spinWeight = signedEvaluation` is proved on
simple coroots using `twice_halfDifference`; it is the safe denominator-free
route to all-root grades and reflection closure. -/
def signedEvaluation (n : ℕ) (σ : Fin (n+1) → Bool) : WeightLattice (pairingB (n+1)) where
  toFun x := ∑ k, sign (σ k) * x.val (Pi.single k 1)
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' t x := by simp [Finset.mul_sum, mul_left_comm]

end Atlas.Chevalley.Integral.Minuscule.TypeB

namespace Atlas.Chevalley.Integral.Minuscule.TypeB
open Classical ClassicalData

/-- The signed coordinate sum has twice the declared fundamental coordinates. -/
theorem signedEvaluation_coordinates (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin (n+1)) :
    weightCoordinates (pairingB (n+1)) (baseB n) (signedEvaluation n σ)
      (baseBIndexEquiv n i) = 2 * spinCoordinates n σ i := by
  rw [weightCoordinates_apply]
  have hb : corootBasis (pairingB (n+1)) (baseB n) (baseBIndexEquiv n i) =
      corootElement (pairingB (n+1)) (simpleB n i) := by
    apply Subtype.ext
    exact (baseB n).flip.coe_toWeightBasisInt_apply
      (⟨simpleB n i, (baseBIndexEquiv n i).property⟩ : (baseB n).flip.support)
  rw [hb]
  change (∑ k, sign (σ k) * coroot (simpleB n i) (Pi.single k 1)) = _
  simp only [simpleB_coroot_vector, functional_apply, dot_single, mul_one]
  unfold chainVector spinCoordinates
  by_cases hi : i.val < n
  · simp [hi, Pi.sub_apply, Pi.single_apply, mul_sub, Finset.sum_sub_distrib,
      twice_halfDifference]
  · simp [hi, Pi.single_apply, mul_comm]

/-- Exact integral half-coordinate identity on the full actual coroot lattice. -/
theorem twice_spinWeight (n : ℕ) (σ : Fin (n+1) → Bool) :
    (2 : ℤ) • spinWeight n σ = signedEvaluation n σ := by
  apply (weightCoordinates (pairingB (n+1)) (baseB n)).injective
  funext j
  obtain ⟨i,rfl⟩ := (baseBIndexEquiv n).surjective j
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, spinWeight_coordinates,
    signedEvaluation_coordinates]

/-- The denominator-free equality is valid on every actual coroot-lattice element. -/
theorem twice_spinWeight_apply (n : ℕ) (σ : Fin (n+1) → Bool)
    (x : CorootLattice (pairingB (n+1))) :
    2 * spinWeight n σ x = ∑ k, sign (σ k) * x.val (Pi.single k 1) := by
  exact congrArg (fun f : WeightLattice (pairingB (n+1)) => f x) (twice_spinWeight n σ)

end Atlas.Chevalley.Integral.Minuscule.TypeB

namespace Atlas.Chevalley.Integral.Minuscule.TypeB
open Classical ClassicalData

/-- Exact spin pairing at each short B root, obtained by integer cancellation. -/
theorem spinWeight_short_pairing (n : ℕ) (σ : Fin (n+1) → Bool)
    (i : Fin (n+1)) (t : ℤ) (ht : t=1 ∨ t= -1) :
    spinWeight n σ (corootElement (pairingB (n+1)) (shortRoot i t ht)) = t * sign (σ i) := by
  have h := twice_spinWeight_apply n σ
    (corootElement (pairingB (n+1)) (shortRoot i t ht))
  change 2 * spinWeight n σ (corootElement (pairingB (n+1)) (shortRoot i t ht)) =
    ∑ k, sign (σ k) * coroot (shortRoot i t ht) (Pi.single k 1) at h
  simp only [coroot_short] at h
  simp [Pi.single_apply, mul_ite, mul_assoc] at h
  nlinarith [h]

/-- Exact doubled spin pairing at each long B root. -/
theorem twice_spinWeight_long_pairing (n : ℕ) (σ : Fin (n+1) → Bool)
    (i j : Fin (n+1)) (hij : i≠j) (t u : ℤ) (ht : t=1 ∨ t= -1) (hu : u=1 ∨ u= -1) :
    2 * spinWeight n σ (corootElement (pairingB (n+1)) (longRoot true i j hij t u ht hu)) =
      t * sign (σ i) + u * sign (σ j) := by
  have h := twice_spinWeight_apply n σ
    (corootElement (pairingB (n+1)) (longRoot true i j hij t u ht hu))
  change 2 * spinWeight n σ (corootElement (pairingB (n+1)) (longRoot true i j hij t u ht hu)) =
    ∑ k, sign (σ k) * coroot (longRoot true i j hij t u ht hu) (Pi.single k 1) at h
  simp only [coroot_long] at h
  simp only [Pi.single_apply, mul_ite, mul_zero, mul_one, mul_add,
    Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  simpa [mul_comm] using h

/-- The spin weights satisfy the minuscule bound for every actual B root. -/
theorem spinWeight_minuscule (n : ℕ) (σ : Fin (n+1) → Bool) (a : BRoot (n+1)) :
    spinWeight n σ (corootElement (pairingB (n+1)) a) = -1 ∨
    spinWeight n σ (corootElement (pairingB (n+1)) a) = 0 ∨
    spinWeight n σ (corootElement (pairingB (n+1)) a) = 1 := by
  rcases signed_support_classification a with ⟨_,i,t,ht,ha⟩ | ⟨i,j,hij,t,u,ht,hu,ha⟩
  · have he : a=shortRoot i t ht := Subtype.ext ha
    subst a
    rw [spinWeight_short_pairing]
    rcases ht with rfl | rfl <;> cases hi : σ i <;> simp [sign, hi]
  · have he : a=longRoot true i j hij t u ht hu := Subtype.ext ha
    subst a
    have h := twice_spinWeight_long_pairing n σ i j hij t u ht hu
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
      cases hi : σ i <;> cases hj : σ j <;> simp [sign, hi, hj] at h <;> omega

/-- Different sign patterns define different actual integral weights. -/
theorem spinWeight_injective (n : ℕ) : Function.Injective (spinWeight n) := by
  intro σ τ h
  funext i
  have hi := congrArg (fun μ : WeightLattice (pairingB (n+1)) =>
    μ (corootElement (pairingB (n+1)) (shortRoot i 1 (Or.inl rfl)))) h
  simp only [spinWeight_short_pairing, one_mul] at hi
  cases hs : σ i <;> cases ht : τ i <;> first | rfl | (norm_num [sign, hs, ht] at hi)

def spinOrbit (n : ℕ) : Finset (WeightLattice (pairingB (n+1))) :=
  Finset.univ.image (spinWeight n)

/-- The spin cardinality is derived from the explicit sign-pattern injection. -/
theorem spinOrbit_card (n : ℕ) : (spinOrbit n).card = 2^(n+1) := by
  rw [spinOrbit, Finset.card_image_of_injective _ (spinWeight_injective n)]
  simp

/-- Root weights for coordinate short roots have literal simple-coroot coordinates. -/
theorem coordinateRootWeight_coordinates (n : ℕ) (k j : Fin (n+1)) :
    weightCoordinates (pairingB (n+1)) (baseB n)
      (rootWeight (pairingB (n+1)) (shortRoot k 1 (Or.inl rfl))) (baseBIndexEquiv n j) =
      chainVector n 2 j k := by
  rw [rootWeight_coordinates]
  change coroot (simpleB n j) (Pi.single k 1) = _
  rw [simpleB_coroot_vector, functional_apply, dot_single, mul_one]

/-- Every non-spin fundamental B weight is an actual integral sum of root weights. -/
theorem nonlast_fundamentalWeight (n : ℕ) (i : Fin (n+1)) (hi : i.val < n) :
    fundamentalWeights (pairingB (n+1)) (baseB n) (baseBIndexEquiv n i) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n+1) => k.val ≤ i.val),
        rootWeight (pairingB (n+1)) (shortRoot k 1 (Or.inl rfl)) := by
  apply (weightCoordinates (pairingB (n+1)) (baseB n)).injective
  funext j
  obtain ⟨j,rfl⟩ := (baseBIndexEquiv n).surjective j
  rw [weightCoordinates_apply, fundamentalWeights_pairing]
  simp only [map_sum, Finset.sum_apply, coordinateRootWeight_coordinates]
  unfold chainVector
  by_cases hj : j.val < n
  · simp [hj, Pi.sub_apply, Pi.single_apply, Finset.sum_sub_distrib]
    simp only [Fin.ext_iff, Fin.le_def, Fin.val_mk]
    split_ifs <;> (try simp only [Fin.le_def, Fin.val_mk] at *) <;> omega
  · simp [hj, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite]
    simp only [Fin.ext_iff, Fin.le_def]
    split_ifs <;> have := j.isLt <;> omega

/-- Root weights and the single chosen spin weight generate the full weight lattice. -/
theorem root_and_spin_weight_span (n : ℕ) :
    Submodule.span ℤ (Set.range (rootWeight (pairingB (n+1))) ∪
      {spinWeight n (fun _ => true)}) = ⊤ := by
  apply top_unique
  rw [← (fundamentalWeights (pairingB (n+1)) (baseB n)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  obtain ⟨i,rfl⟩ := (baseBIndexEquiv n).surjective j
  by_cases hi : i.val < n
  · rw [nonlast_fundamentalWeight n i hi]
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.subset_span (Or.inl ⟨_,rfl⟩)
  · have he : i=Fin.last n := Fin.ext (by change i.val=n; have := i.isLt; omega)
    rw [he, ← positive_spinWeight]
    exact Submodule.subset_span (Or.inr rfl)

end Atlas.Chevalley.Integral.Minuscule.TypeB

namespace Atlas.Chevalley.Integral.Minuscule.TypeB
open Classical ClassicalData

/-- Doubled spin weights are represented by literal signed coordinate vectors. -/
def signVector (n : ℕ) (σ : Fin (n+1) → Bool) : ClassicalData.Lattice (n+1) := fun k => sign (σ k)

theorem signVector_expansion (n : ℕ) (σ : Fin (n+1) → Bool) :
    signVector n σ = ∑ k, sign (σ k) • (Pi.single k 1 : Fin (n+1) → ℤ) := by
  ext j
  simp [signVector, Pi.single_apply]

theorem twice_spinWeight_evaluation (n : ℕ) (σ : Fin (n+1) → Bool)
    (x : CorootLattice (pairingB (n+1))) :
    2 * spinWeight n σ x = x.val (signVector n σ) := by
  rw [twice_spinWeight_apply, signVector_expansion]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The actual root reflection on a signed pair is a signed exchange. -/
theorem reflect_long_coordinates {r : ℕ} (i j : Fin r) (hij : i≠j)
    (t u : ℤ) (ht : t=1 ∨ t= -1) (hu : u=1 ∨ u= -1) (x : ClassicalData.Lattice r) (k : Fin r) :
    reflect (longRoot true i j hij t u ht hu) x k =
      if k=i then -t*u*x j else if k=j then -t*u*x i else x k := by
  change (x - coroot (longRoot true i j hij t u ht hu) x •
    (longRoot true i j hij t u ht hu).val) k = _
  rw [coroot_long]
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    by_cases hi : k=i <;> by_cases hj : k=j <;>
    simp [longRoot, Pi.single_apply, hi, hj, hij, eq_comm] <;>
    first | (subst k; contradiction) | ring

/-- Every actual B reflection preserves the explicit sign-vector set. -/
theorem reflected_sign (n : ℕ) (a : BRoot (n+1)) (σ : Fin (n+1) → Bool) (k : Fin (n+1)) :
    reflect a (signVector n σ) k = 1 ∨ reflect a (signVector n σ) k = -1 := by
  rcases signed_support_classification a with ⟨_,i,t,ht,ha⟩ | ⟨i,j,hij,t,u,ht,hu,ha⟩
  · have he : a=shortRoot i t ht := Subtype.ext ha
    subst a
    rw [reflect_short]
    split_ifs <;> cases hk : σ k <;> simp [signVector, sign, hk]
  · have he : a=longRoot true i j hij t u ht hu := Subtype.ext ha
    subst a
    rw [reflect_long_coordinates]
    split_ifs <;> rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
      cases hσi : σ i <;> cases hσj : σ j <;> cases hσk : σ k <;>
      simp [signVector, sign, hσi, hσj, hσk]

/-- The root acts on sign codes by its actual coordinate reflection. -/
def reflectedSigns (n : ℕ) (a : BRoot (n+1)) (σ : Fin (n+1) → Bool) : Fin (n+1) → Bool :=
  fun k => decide (reflect a (signVector n σ) k = 1)

theorem signVector_reflectedSigns (n : ℕ) (a : BRoot (n+1)) (σ : Fin (n+1) → Bool) :
    signVector n (reflectedSigns n a σ) = reflect a (signVector n σ) := by
  ext k
  rcases reflected_sign n a σ k with h | h <;> simp [signVector, reflectedSigns, sign, h]

/-- Exact compatibility of the doubled integral model with actual weight reflections. -/
theorem twice_reflected_spin_evaluation (n : ℕ) (a : BRoot (n+1))
    (σ : Fin (n+1) → Bool) (x : CorootLattice (pairingB (n+1))) :
    2 * weightReflection (pairingB (n+1)) a (spinWeight n σ) x =
      x.val (reflect a (signVector n σ)) := by
  have hx := twice_spinWeight_evaluation n σ x
  have ha := twice_spinWeight_evaluation n σ (corootElement (pairingB (n+1)) a)
  change 2 * spinWeight n σ (corootElement (pairingB (n+1)) a) =
    coroot a (signVector n σ) at ha
  change 2 * (spinWeight n σ x -
      spinWeight n σ (corootElement (pairingB (n+1)) a) * x.val a.val) = _
  change _ = x.val (signVector n σ - coroot a (signVector n σ) • a.val)
  rw [map_sub, map_smul]
  simp only [smul_eq_mul]
  rw [← hx, ← ha]
  ring

/-- Every actual root acts on the constructed spin weights by the explicit sign action. -/
theorem spinWeight_reflection (n : ℕ) (a : BRoot (n+1)) (σ : Fin (n+1) → Bool) :
    weightReflection (pairingB (n+1)) a (spinWeight n σ) =
      spinWeight n (reflectedSigns n a σ) := by
  ext x
  have h₁ := twice_reflected_spin_evaluation n a σ x
  have h₂ := twice_spinWeight_evaluation n (reflectedSigns n a σ) x
  rw [signVector_reflectedSigns] at h₂
  omega

theorem spinOrbit_closed (n : ℕ) (a : BRoot (n+1)) (μ : WeightLattice (pairingB (n+1)))
    (hμ : μ ∈ spinOrbit n) : weightReflection (pairingB (n+1)) a μ ∈ spinOrbit n := by
  obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hμ
  rw [spinWeight_reflection]
  exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

end Atlas.Chevalley.Integral.Minuscule.TypeB

namespace Atlas.Chevalley.Integral.Minuscule.TypeB
open Classical ClassicalData

/-- Short-root reflections change exactly one Boolean sign. -/
theorem short_reflectedSigns (n : ℕ) (i : Fin (n+1)) (σ : Fin (n+1) → Bool) :
    reflectedSigns n (shortRoot i 1 (Or.inl rfl)) σ = Function.update σ i (!(σ i)) := by
  funext k
  by_cases hk : k=i
  · subst k
    cases h : σ i <;> simp [reflectedSigns, reflect_short, signVector, sign, h]
  · cases h : σ k <;> simp [reflectedSigns, reflect_short, signVector, sign, hk, h]

def ReflectionStep (n : ℕ) (μ ν : WeightLattice (pairingB (n+1))) : Prop :=
  ∃ a : BRoot (n+1), weightReflection (pairingB (n+1)) a μ = ν

theorem update_reachable (n : ℕ) (σ : Fin (n+1) → Bool) (i : Fin (n+1)) (t : Bool) :
    Relation.ReflTransGen (ReflectionStep n) (spinWeight n σ)
      (spinWeight n (Function.update σ i t)) := by
  by_cases h : σ i=t
  · have he : Function.update σ i t=σ := by rw [← h]; exact Function.update_eq_self _ _
    rw [he]
  · have ht : t= !(σ i) := by cases hs : σ i <;> cases t <;> simp_all
    apply Relation.ReflTransGen.single
    refine ⟨shortRoot i 1 (Or.inl rfl), ?_⟩
    rw [spinWeight_reflection, short_reflectedSigns, ← ht]

/-- Finite coordinate updates give actual spin-weight reflection transitivity. -/
theorem spinWeight_reachable (n : ℕ) (σ τ : Fin (n+1) → Bool) :
    Relation.ReflTransGen (ReflectionStep n) (spinWeight n σ) (spinWeight n τ) := by
  have aux : ∀ s : Finset (Fin (n+1)), ∀ σ τ : Fin (n+1) → Bool,
      (∀ i, i ∉ s → σ i=τ i) →
      Relation.ReflTransGen (ReflectionStep n) (spinWeight n σ) (spinWeight n τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro σ τ h
      have he : σ=τ := funext (fun i => h i (by simp))
      rw [he]
    | @insert i s hi ih =>
      intro σ τ h
      let σ' := Function.update σ i (τ i)
      have hrest : ∀ j, j ∉ s → σ' j=τ j := by
        intro j hj
        by_cases hji : j=i
        · subst j; simp [σ']
        · simp only [σ', Function.update_of_ne hji]
          exact h j (by simp [hj, hji])
      exact (update_reachable n σ i (τ i)).trans (ih σ' τ hrest)
  exact aux Finset.univ σ τ (by simp)

theorem spinOrbit_transitive (n : ℕ) (μ ν : WeightLattice (pairingB (n+1)))
    (hμ : μ ∈ spinOrbit n) (hν : ν ∈ spinOrbit n) :
    Relation.ReflTransGen (ReflectionStep n) μ ν := by
  obtain ⟨σ,_,rfl⟩ := Finset.mem_image.mp hμ
  obtain ⟨τ,_,rfl⟩ := Finset.mem_image.mp hν
  exact spinWeight_reachable n σ τ

end Atlas.Chevalley.Integral.Minuscule.TypeB
