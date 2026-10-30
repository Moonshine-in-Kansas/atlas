import Atlas.LinearGroups.Chevalley.TwistedE6.FixedParameters

/-! Compatible scalar functions supported on an arbitrary diagram-stable subset.

The reconstruction and extraction maps reuse `PositiveDiagramParameters.assemble`
and `extract`, after extending the selected orbit coordinates by zero. The
singleton-plus-two-times-pair identity is proved by an explicit orbit-label
bijection for the given subset, without enumerating subsets or group elements.

This is a parameter-space statement only. Exact staged verification receipts
are recorded separately. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Atlas.Chevalley.TwistedE6.PositiveDiagramParameters

/-- Existing fixed labels whose actual positive-root label lies in S. -/
abbrev SubsetFixedLabel (S : Set (Fin 36)) := {i : FixedLabel // i.val ∈ S}

/-- Existing smaller pair representatives whose actual label lies in S. -/
abbrev SubsetPairLabel (S : Set (Fin 36)) := {i : PairLabel // i.val ∈ S}

abbrev SubsetParameters (F K : Type*) (S : Set (Fin 36)) :=
  (SubsetFixedLabel S → F) × (SubsetPairLabel S → K)

theorem subsetDiagram_mem_iff (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (i : Fin 36) :
    positiveDiagram i ∈ S ↔ i ∈ S := by
  constructor
  · intro hi
    simpa only [positiveDiagram_involutive i] using hS (positiveDiagram i) hi
  · exact hS i

/-- The two copies of a pair representative mark its smaller and larger labels. -/
def subsetOrbitLabelMap (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) :
    SubsetFixedLabel S ⊕ (SubsetPairLabel S ⊕ SubsetPairLabel S) → S
  | .inl i => ⟨i.val.val, i.property⟩
  | .inr (.inl i) => ⟨i.val.val, i.property⟩
  | .inr (.inr i) => ⟨positiveDiagram i.val.val, hS i.val.val i.property⟩

def subsetOrbitLabelExtract (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (i : S) :
    SubsetFixedLabel S ⊕ (SubsetPairLabel S ⊕ SubsetPairLabel S) :=
  if hfix : positiveDiagram i.val = i.val then
    .inl ⟨⟨i.val, hfix⟩, i.property⟩
  else if hlt : i.val < positiveDiagram i.val then
    .inr (.inl ⟨⟨i.val, hlt⟩, i.property⟩)
  else
    .inr (.inr ⟨⟨positiveDiagram i.val, by
      rw [positiveDiagram_involutive]
      exact lt_of_le_of_ne (le_of_not_gt hlt) hfix⟩, hS i.val i.property⟩)

theorem subsetOrbitLabelMap_extract (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (i : S) :
    subsetOrbitLabelMap S hS (subsetOrbitLabelExtract S hS i) = i := by
  apply Subtype.ext
  by_cases hfix : positiveDiagram i.val = i.val
  · simp only [subsetOrbitLabelExtract, dif_pos hfix, subsetOrbitLabelMap]
  · by_cases hlt : i.val < positiveDiagram i.val
    · simp only [subsetOrbitLabelExtract, dif_neg hfix, dif_pos hlt, subsetOrbitLabelMap]
    · simp only [subsetOrbitLabelExtract, dif_neg hfix, dif_neg hlt,
        subsetOrbitLabelMap, positiveDiagram_involutive i.val]

theorem subsetOrbitLabelExtract_map (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S)
    (p : SubsetFixedLabel S ⊕ (SubsetPairLabel S ⊕ SubsetPairLabel S)) :
    subsetOrbitLabelExtract S hS (subsetOrbitLabelMap S hS p) = p := by
  rcases p with i | (i | i)
  · dsimp only [subsetOrbitLabelMap]
    unfold subsetOrbitLabelExtract
    split_ifs with hfix hlt
    · rfl
    · exact False.elim (hfix i.val.property)
    · exact False.elim (hfix i.val.property)
  · have hfix : positiveDiagram i.val.val ≠ i.val.val := ne_of_gt i.val.property
    dsimp only [subsetOrbitLabelMap]
    unfold subsetOrbitLabelExtract
    split_ifs with hfixed hlt
    · exact False.elim (hfix hfixed)
    · rfl
    · exact False.elim (hlt i.val.property)
  · have hfix : positiveDiagram (positiveDiagram i.val.val) ≠ positiveDiagram i.val.val := by
      rw [positiveDiagram_involutive]
      exact ne_of_lt i.val.property
    have hlt : ¬ positiveDiagram i.val.val < positiveDiagram (positiveDiagram i.val.val) := by
      rw [positiveDiagram_involutive]
      exact not_lt_of_ge i.val.property.le
    dsimp only [subsetOrbitLabelMap]
    unfold subsetOrbitLabelExtract
    split_ifs with hfixed hless <;> try contradiction
    apply congrArg (fun j : SubsetPairLabel S =>
      (Sum.inr (Sum.inr j) : SubsetFixedLabel S ⊕ (SubsetPairLabel S ⊕ SubsetPairLabel S)))
    apply Subtype.ext
    apply Subtype.ext
    exact positiveDiagram_involutive i.val.val

/-- An actual orbit partition of S, not a comparison using the counts of all 36 labels. -/
def subsetOrbitLabelsEquiv (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) :
    (SubsetFixedLabel S ⊕ (SubsetPairLabel S ⊕ SubsetPairLabel S)) ≃ S where
  toFun := subsetOrbitLabelMap S hS
  invFun := subsetOrbitLabelExtract S hS
  left_inv := subsetOrbitLabelExtract_map S hS
  right_inv := subsetOrbitLabelMap_extract S hS

theorem subset_card_eq_fixed_add_twice_pair (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) :
    Nat.card S = Nat.card (SubsetFixedLabel S) + 2 * Nat.card (SubsetPairLabel S) := by
  calc
    _ = Nat.card (SubsetFixedLabel S ⊕ (SubsetPairLabel S ⊕ SubsetPairLabel S)) :=
      (Nat.card_congr (subsetOrbitLabelsEquiv S hS)).symm
    _ = _ := by rw [Nat.card_sum, Nat.card_sum, two_mul]

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Literal compatible functions on all 36 labels, with zero coordinates outside S. -/
def SubsetFixedFunctions (S : Set (Fin 36)) :=
  {f : Fin 36 → K //
    (∀ i, f (positiveDiagram i) = Atlas.FiniteQuadratic.conjugation F K (f i)) ∧
      (∀ i, i ∉ S → f i = 0)}

def subsetFixedFunctionsForget (S : Set (Fin 36))
    (f : SubsetFixedFunctions F K S) : FixedFunctions F K :=
  ⟨f.val, f.property.1⟩

def restrictSubsetParameters (S : Set (Fin 36)) (p : Parameters F K) :
    SubsetParameters F K S :=
  (fun i => p.1 i.val, fun i => p.2 i.val)

/-- Extend each type of orbit coordinate separately, retaining the existing marking. -/
def extendSubsetParameters (S : Set (Fin 36)) (p : SubsetParameters F K S) :
    Parameters F K := by
  classical
  exact (fun i => if hi : i.val ∈ S then p.1 ⟨i, hi⟩ else 0,
    fun i => if hi : i.val ∈ S then p.2 ⟨i, hi⟩ else 0)

theorem extendSubsetParameters_fixed_off (S : Set (Fin 36))
    (p : SubsetParameters F K S) (i : FixedLabel) (hi : i.val ∉ S) :
    (extendSubsetParameters F K S p).1 i = 0 := by
  classical
  simp only [extendSubsetParameters, dif_neg hi]

theorem extendSubsetParameters_pair_off (S : Set (Fin 36))
    (p : SubsetParameters F K S) (i : PairLabel) (hi : i.val ∉ S) :
    (extendSubsetParameters F K S p).2 i = 0 := by
  classical
  simp only [extendSubsetParameters, dif_neg hi]

theorem restrict_extendSubsetParameters (S : Set (Fin 36)) (p : SubsetParameters F K S) :
    restrictSubsetParameters F K S (extendSubsetParameters F K S p) = p := by
  classical
  apply Prod.ext
  · funext i
    simp only [restrictSubsetParameters, extendSubsetParameters, dif_pos i.property]
  · funext i
    simp only [restrictSubsetParameters, extendSubsetParameters, dif_pos i.property]

/-- The existing expansion vanishes off S when its orbit coordinates do.
Only the three generic orbit positions are used, never individual label cases. -/
theorem expand_extendSubsetParameters_zero_off (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S)
    (p : SubsetParameters F K S) (i : Fin 36) (hi : i ∉ S) :
    expand F K (extendSubsetParameters F K S p) i = 0 := by
  by_cases hfix : positiveDiagram i = i
  · rw [expand_fixed F K _ ⟨i, hfix⟩,
      extendSubsetParameters_fixed_off F K S p ⟨i, hfix⟩ hi, map_zero]
  · by_cases hlt : i < positiveDiagram i
    · rw [expand_pair F K _ ⟨i, hlt⟩,
        extendSubsetParameters_pair_off F K S p ⟨i, hlt⟩ hi]
    · have hgt : positiveDiagram i < i := lt_of_le_of_ne (le_of_not_gt hlt) hfix
      let j : PairLabel := ⟨positiveDiagram i, by
        rw [positiveDiagram_involutive]
        exact hgt⟩
      have hj : positiveDiagram j.val = i := positiveDiagram_involutive i
      have hjnot : j.val ∉ S := by
        intro hjmem
        exact hi ((subsetDiagram_mem_iff S hS i).mp hjmem)
      calc
        expand F K (extendSubsetParameters F K S p) i =
            expand F K (extendSubsetParameters F K S p) (positiveDiagram j.val) :=
          congrArg (expand F K (extendSubsetParameters F K S p)) hj.symm
        _ = Atlas.FiniteQuadratic.conjugation F K ((extendSubsetParameters F K S p).2 j) :=
          expand_partner F K (extendSubsetParameters F K S p) j
        _ = 0 := by rw [extendSubsetParameters_pair_off F K S p j hjnot, map_zero]

/-- Reuse the full assembly after zero-extension of the selected orbit coordinates. -/
def subsetAssemble (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (hdeg : Module.finrank F K = 2)
    (p : SubsetParameters F K S) : SubsetFixedFunctions F K S :=
  ⟨(assemble F K hdeg (extendSubsetParameters F K S p)).val,
    (assemble F K hdeg (extendSubsetParameters F K S p)).property,
    expand_extendSubsetParameters_zero_off F K S hS p⟩

/-- Reuse full extraction and retain just the orbit coordinates belonging to S. -/
def subsetExtract (S : Set (Fin 36)) (hdeg : Module.finrank F K = 2)
    (f : SubsetFixedFunctions F K S) : SubsetParameters F K S :=
  restrictSubsetParameters F K S
    (extract F K hdeg (subsetFixedFunctionsForget F K S f))

/-- The discarded orbit coordinates were zero already. -/
theorem extend_subsetExtract (S : Set (Fin 36)) (hdeg : Module.finrank F K = 2)
    (f : SubsetFixedFunctions F K S) :
    extendSubsetParameters F K S (subsetExtract F K S hdeg f) =
      extract F K hdeg (subsetFixedFunctionsForget F K S f) := by
  classical
  apply Prod.ext
  · funext i
    by_cases hi : i.val ∈ S
    · simp only [extendSubsetParameters, dif_pos hi, subsetExtract, restrictSubsetParameters]
    · rw [extendSubsetParameters_fixed_off F K S _ i hi]
      symm
      apply (algebraMap F K).injective
      calc
        algebraMap F K ((extract F K hdeg (subsetFixedFunctionsForget F K S f)).1 i) =
            f.val i.val := extract_fixed_val F K hdeg (subsetFixedFunctionsForget F K S f) i
        _ = 0 := f.property.2 i.val hi
        _ = algebraMap F K 0 := (map_zero (algebraMap F K)).symm
  · funext i
    by_cases hi : i.val ∈ S
    · simp only [extendSubsetParameters, dif_pos hi, subsetExtract, restrictSubsetParameters]
    · rw [extendSubsetParameters_pair_off F K S _ i hi]
      symm
      change f.val i.val = 0
      exact f.property.2 i.val hi

theorem subsetAssemble_extract (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (hdeg : Module.finrank F K = 2)
    (f : SubsetFixedFunctions F K S) :
    subsetAssemble F K S hS hdeg (subsetExtract F K S hdeg f) = f := by
  apply Subtype.ext
  change (assemble F K hdeg
    (extendSubsetParameters F K S (subsetExtract F K S hdeg f))).val = f.val
  rw [extend_subsetExtract F K S hdeg f]
  exact congrArg (fun g : FixedFunctions F K => g.val)
    (assemble_extract F K hdeg (subsetFixedFunctionsForget F K S f))

theorem subsetExtract_assemble (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (hdeg : Module.finrank F K = 2)
    (p : SubsetParameters F K S) :
    subsetExtract F K S hdeg (subsetAssemble F K S hS hdeg p) = p := by
  change restrictSubsetParameters F K S
    (extract F K hdeg (assemble F K hdeg (extendSubsetParameters F K S p))) = p
  rw [extract_assemble, restrict_extendSubsetParameters]

/-- All supported compatible functions, with one F coordinate per selected
singleton and one K coordinate per selected smaller pair representative. -/
def subsetFixedFunctionsEquiv (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (hdeg : Module.finrank F K = 2) :
    SubsetFixedFunctions F K S ≃ SubsetParameters F K S where
  toFun := subsetExtract F K S hdeg
  invFun := subsetAssemble F K S hS hdeg
  left_inv := subsetAssemble_extract F K S hS hdeg
  right_inv := subsetExtract_assemble F K S hS hdeg

theorem subsetFixedFunctionsEquiv_apply_fixed (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (hdeg : Module.finrank F K = 2)
    (f : SubsetFixedFunctions F K S) (i : SubsetFixedLabel S) :
    algebraMap F K ((subsetFixedFunctionsEquiv F K S hS hdeg f).1 i) = f.val i.val.val :=
  extract_fixed_val F K hdeg (subsetFixedFunctionsForget F K S f) i.val

@[simp] theorem subsetFixedFunctionsEquiv_apply_pair (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (hdeg : Module.finrank F K = 2)
    (f : SubsetFixedFunctions F K S) (i : SubsetPairLabel S) :
    (subsetFixedFunctionsEquiv F K S hS hdeg f).2 i = f.val i.val.val := rfl

@[simp] theorem subsetFixedFunctionsEquiv_symm_val (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (hdeg : Module.finrank F K = 2)
    (p : SubsetParameters F K S) (i : Fin 36) :
    ((subsetFixedFunctionsEquiv F K S hS hdeg).symm p).val i =
      expand F K (extendSubsetParameters F K S p) i := rfl

theorem subsetParameters_card (S : Set (Fin 36)) :
    Nat.card (SubsetParameters F K S) =
      Nat.card F ^ Nat.card (SubsetFixedLabel S) * Nat.card K ^ Nat.card (SubsetPairLabel S) := by
  change Nat.card ((SubsetFixedLabel S → F) × (SubsetPairLabel S → K)) = _
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fun]

/-- Count only the parameter space; there is no group membership or generation premise. -/
theorem subsetFixedFunctions_card (S : Set (Fin 36))
    (hS : ∀ i, i ∈ S → positiveDiagram i ∈ S) (hdeg : Module.finrank F K = 2) :
    Nat.card (SubsetFixedFunctions F K S) = Nat.card F ^ Nat.card S := by
  calc
    _ = Nat.card (SubsetParameters F K S) :=
      Nat.card_congr (subsetFixedFunctionsEquiv F K S hS hdeg)
    _ = Nat.card F ^ Nat.card (SubsetFixedLabel S) *
        Nat.card K ^ Nat.card (SubsetPairLabel S) := subsetParameters_card F K S
    _ = Nat.card F ^ (Nat.card (SubsetFixedLabel S) + 2 * Nat.card (SubsetPairLabel S)) := by
      rw [Atlas.FiniteQuadratic.card_extension hdeg, pow_add, pow_mul]
    _ = Nat.card F ^ Nat.card S :=
      congrArg (fun n : ℕ => Nat.card F ^ n) (subset_card_eq_fixed_add_twice_pair S hS).symm

end Atlas.Chevalley.TwistedE6.PositiveDiagramParameters
