import Atlas.LinearGroups.Chevalley.RootData.A
import Atlas.LinearGroups.Chevalley.Integral.MinusculeWeightLattice
import Mathlib.Tactic

/-! Actual A defining weights. The full weight lattice is the
integral dual of the already constructed coroot lattice. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeA
open Classical
open TypeAData

/-- The k-th defining weight is evaluation of a coroot functional at e_k. -/
def naturalWeight {n : ℕ} (k : Fin n) : WeightLattice (pairing n) where
  toFun f := f.val (Pi.single k 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact pairing with every actual root coroot, not just simple coroots. -/
theorem naturalWeight_pairing {n : ℕ} (k : Fin n) (a : Root n) :
    naturalWeight k (corootElement (pairing n) a) =
      (if a.val.1 = k then 1 else 0) - (if a.val.2 = k then 1 else 0) := by
  change (Pi.single k (1 : ℤ) : Fin n → ℤ) a.val.1 - (Pi.single k (1 : ℤ) : Fin n → ℤ) a.val.2 = _
  simp [Pi.single_apply]

/-- Defining weights satisfy the minuscule bound for every root. -/
theorem naturalWeight_minuscule {n : ℕ} (k : Fin n) (a : Root n) :
    naturalWeight k (corootElement (pairing n) a) = -1 ∨
    naturalWeight k (corootElement (pairing n) a) = 0 ∨
    naturalWeight k (corootElement (pairing n) a) = 1 := by
  rw [naturalWeight_pairing]
  split_ifs <;> norm_num

/-- Every actual A root is the difference of its endpoint defining weights. -/
theorem rootWeight_eq_difference {n : ℕ} (a : Root n) :
    rootWeight (pairing n) a = naturalWeight a.val.1 - naturalWeight a.val.2 := by
  ext f
  change f.val (Pi.single a.val.1 1 - Pi.single a.val.2 1) = _
  exact map_sub f.val _ _

/-- The root reflection acts by the literal transposition of defining weights. -/
theorem naturalWeight_reflection {n : ℕ} (a : Root n) (k : Fin n) :
    weightReflection (pairing n) a (naturalWeight k) =
      naturalWeight (Equiv.swap a.val.1 a.val.2 k) := by
  rw [weightReflection_apply, naturalWeight_pairing, rootWeight_eq_difference]
  by_cases h₁ : k = a.val.1
  · subst k
    simp [a.property, Ne.symm a.property]
  · by_cases h₂ : k = a.val.2
    · subst k
      simp [a.property, Ne.symm a.property]
    · simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂, Equiv.swap_apply_of_ne_of_ne]

/-- No accidental collapse of the defining weights occurs inside the dual lattice. -/
theorem naturalWeight_injective (n : ℕ) : Function.Injective (@naturalWeight n) := by
  intro i j h
  by_contra hij
  let a : Root n := ⟨(i, j), hij⟩
  have he := congrArg (fun μ : WeightLattice (pairing n) => μ (corootElement (pairing n) a)) h
  simpa [naturalWeight_pairing, a, hij, Ne.symm hij] using he

/-- Actual finite defining orbit, not a supplied target cardinality. -/
def naturalOrbit (r : ℕ) : Finset (WeightLattice (pairing (r + 1))) :=
  Finset.univ.image naturalWeight

theorem naturalOrbit_card (r : ℕ) : (naturalOrbit r).card = r + 1 := by
  rw [naturalOrbit, Finset.card_image_of_injective _ (naturalWeight_injective _)]
  exact Fintype.card_fin _

theorem naturalOrbit_closed (r : ℕ) (a : Root (r + 1))
    (μ : WeightLattice (pairing (r + 1))) (hμ : μ ∈ naturalOrbit r) :
    weightReflection (pairing (r + 1)) a μ ∈ naturalOrbit r := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hμ
  rw [naturalWeight_reflection]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- Every defining weight can be obtained from any other in one root reflection
(or zero reflections when they agree). This is actual orbit transitivity. -/
theorem naturalOrbit_transitive (r : ℕ) (i j : Fin (r + 1)) :
    i = j ∨ ∃ a : Root (r + 1),
      weightReflection (pairing (r + 1)) a (naturalWeight i) = naturalWeight j := by
  by_cases hij : i = j
  · exact Or.inl hij
  · right
    refine ⟨⟨(i,j),hij⟩, ?_⟩
    rw [naturalWeight_reflection]
    simp

/-- Fundamental weight λ_i is the prefix sum of the actual defining weights. -/
theorem fundamentalWeight_eq_prefix (r : ℕ) (i : Fin r) :
    fundamentalWeights (pairing (r + 1)) (base r) (baseIndexEquiv r i) =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (r + 1) => k.val ≤ i.val), naturalWeight k := by
  apply (corootBasis (pairing (r + 1)) (base r)).ext
  intro j
  obtain ⟨j, rfl⟩ := (baseIndexEquiv r).surjective j
  rw [fundamentalWeights_pairing]
  have hb : corootBasis (pairing (r+1)) (base r) (baseIndexEquiv r j) =
      corootElement (pairing (r+1)) (simpleRoot j) := by
    apply Subtype.ext
    exact (base r).flip.coe_toWeightBasisInt_apply
      (⟨simpleRoot j, (baseIndexEquiv r j).property⟩ : (base r).flip.support)
  rw [hb]
  simp [naturalWeight_pairing, simpleRoot, LinearMap.sum_apply,
    Finset.sum_sub_distrib]
  simp only [Fin.ext_iff, Fin.le_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- The actual defining orbit spans the full weight lattice integrally. -/
theorem naturalOrbit_span (r : ℕ) :
    Submodule.span ℤ (Set.range (@naturalWeight (r + 1))) = ⊤ := by
  apply top_unique
  rw [← (fundamentalWeights (pairing (r + 1)) (base r)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  obtain ⟨i, rfl⟩ := (baseIndexEquiv r).surjective j
  rw [fundamentalWeight_eq_prefix]
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.subset_span ⟨k, rfl⟩

/-- The actual root lattice together with a single chosen defining weight
already spans P. This is the required A-family P/Q generation statement. -/
theorem root_and_one_weight_span (r : ℕ) :
    Submodule.span ℤ (Set.range (rootWeight (pairing (r + 1))) ∪
      {naturalWeight (0 : Fin (r + 1))}) = ⊤ := by
  apply top_unique
  rw [← naturalOrbit_span r]
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  by_cases hk : k = 0
  · subst k
    exact Submodule.subset_span (Or.inr rfl)
  · let a : Root (r + 1) := ⟨(k,0),hk⟩
    have hroot : rootWeight (pairing (r + 1)) a ∈
        Submodule.span ℤ (Set.range (rootWeight (pairing (r + 1))) ∪
          {naturalWeight (0 : Fin (r + 1))}) := Submodule.subset_span (Or.inl ⟨a,rfl⟩)
    have hzero : naturalWeight (0 : Fin (r + 1)) ∈
        Submodule.span ℤ (Set.range (rootWeight (pairing (r + 1))) ∪
          {naturalWeight (0 : Fin (r + 1))}) := Submodule.subset_span (Or.inr rfl)
    simpa [rootWeight_eq_difference, a] using Submodule.add_mem _ hroot hzero

end Atlas.Chevalley.Integral.Minuscule.TypeA
