import Atlas.LinearGroups.Chevalley.TwistedE6.DualMinuscule
import Atlas.LinearGroups.Chevalley.Integral.E6Minuscule.Strings

/-! The second actual minuscule orbit and the diagram covariance of its
simple-root strings. Adjoining this orbit retains the existing selected
companion by literal block restriction, not by group-order recognition. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open Classical E6Data Integral.Minuscule

def negativeWeights : Finset (WeightLattice pairing) :=
  E6Minuscule.weights.image Neg.neg

theorem negativeWeights_closed (i : Root) (μ : WeightLattice pairing)
    (hμ : μ ∈ negativeWeights) : weightReflection pairing i μ ∈ negativeWeights := by
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
  exact Finset.mem_image.mpr ⟨weightReflection pairing i ν,
    E6Minuscule.weights_closed i ν hν, (map_neg _ _).symm⟩

theorem negativeWeights_minuscule (μ : WeightLattice pairing)
    (hμ : μ ∈ negativeWeights) (i : Root) :
    μ (corootElement pairing i) = -1 ∨ μ (corootElement pairing i) = 0 ∨
      μ (corootElement pairing i) = 1 := by
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
  have h : ν (corootElement pairing i) = -1 ∨ ν (corootElement pairing i) = 0 ∨
      ν (corootElement pairing i) = 1 :=
    by
      obtain ⟨j, rfl⟩ := (E6Minuscule.mem_weights ν).mp hν
      exact E6Minuscule.all_root_grades j i
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by simp [h]))
  · exact Or.inr (Or.inl (by simp [h]))
  · exact Or.inl (by simp [h])

theorem weightDiagram_mem_negative (μ : WeightLattice pairing)
    (hμ : μ ∈ E6Minuscule.weights) : weightDiagram μ ∈ negativeWeights := by
  obtain ⟨ν, hν, h⟩ := weightDiagram_mem_negative_orbit μ hμ
  exact Finset.mem_image.mpr ⟨ν, hν, h.symm⟩

theorem weightDiagram_mem_positive (μ : WeightLattice pairing)
    (hμ : μ ∈ negativeWeights) : weightDiagram μ ∈ E6Minuscule.weights := by
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
  obtain ⟨ξ, hξ, h⟩ := weightDiagram_mem_negative_orbit ν hν
  simpa only [map_neg, h, neg_neg] using hξ

private theorem corootBasis_eq (i : base.support) :
    corootBasis pairing base i = corootElement pairing i.val := by
  apply Subtype.ext
  exact base.flip.coe_toWeightBasisInt_apply i

theorem weightDiagram_simple_grade (μ : WeightLattice pairing) (i : base.support) :
    weightDiagram μ (corootElement pairing (baseDiagram i).val) =
      μ (corootElement pairing i.val) := by
  obtain ⟨j, rfl⟩ := baseIndexEquiv.surjective i
  have h := congrFun (weightDiagram_coordinates μ) (simpleNode j)
  simpa only [indexedWeightCoordinates_apply, coordinateDiagram_apply,
    simpleNode_involutive j, baseDiagram_index, corootBasis_eq] using h

theorem weightDiagram_simple_root (i : base.support) :
    weightDiagram (rootWeight pairing i.val) = rootWeight pairing (baseDiagram i).val := by
  apply (indexedWeightCoordinates pairing base baseIndexEquiv).injective
  funext j
  rw [weightDiagram_coordinates, coordinateDiagram_apply]
  change weightCoordinates pairing base (rootWeight pairing i.val)
      (baseIndexEquiv (simpleNode j)) =
    weightCoordinates pairing base (rootWeight pairing (baseDiagram i).val) (baseIndexEquiv j)
  rw [simpleRootWeight_coordinates, simpleRootWeight_coordinates, ← baseDiagram_index]
  have h := baseDiagram_cartan i (baseDiagram (baseIndexEquiv j))
  simpa only [baseDiagram_involutive (baseIndexEquiv j)] using h.symm

theorem weightDiagram_simple_reflection (i : base.support) (μ : WeightLattice pairing) :
    weightDiagram (weightReflection pairing i.val μ) =
      weightReflection pairing (baseDiagram i).val (weightDiagram μ) := by
  simp only [weightReflection_apply, map_sub, map_smul,
    weightDiagram_simple_root, weightDiagram_simple_grade]

/-- The negative block and the original block in the established adjoining API. -/
abbrev dualOrbits : Option Unit → Finset (WeightLattice pairing)
  | none => negativeWeights
  | some _ => E6Minuscule.weights

theorem dualOrbits_closed : ∀ a i μ, μ ∈ dualOrbits a →
    weightReflection pairing i μ ∈ dualOrbits a := by
  intro a
  cases a with
  | none => exact negativeWeights_closed
  | some a => exact E6Minuscule.weights_closed

theorem dualOrbits_minuscule : ∀ a μ, μ ∈ dualOrbits a → ∀ i,
    μ (corootElement pairing i) = -1 ∨ μ (corootElement pairing i) = 0 ∨
      μ (corootElement pairing i) = 1 := by
  intro a μ hμ i
  cases a with
  | none => exact negativeWeights_minuscule μ hμ i
  | some a =>
    obtain ⟨j, rfl⟩ := (E6Minuscule.mem_weights μ).mp hμ
    exact E6Minuscule.all_root_grades j i

def dualBlockSwap : Equiv.Perm (Option Unit) where
  toFun | none => some () | some _ => none
  invFun | none => some () | some _ => none
  left_inv a := by cases a with | none => rfl | some a => cases a; rfl
  right_inv a := by cases a with | none => rfl | some a => cases a; rfl

theorem dualBlockSwap_involutive : Function.Involutive dualBlockSwap := by
  intro a
  cases a with | none => rfl | some a => cases a; rfl

theorem weightDiagram_mem_dualOrbit (a : Option Unit)
    (μ : WeightLattice pairing) (hμ : μ ∈ dualOrbits a) :
    weightDiagram μ ∈ dualOrbits (dualBlockSwap a) := by
  cases a with
  | none => exact weightDiagram_mem_positive μ hμ
  | some a => exact weightDiagram_mem_negative μ hμ

def dualOrbitDiagram (a : Option Unit) :
    WeightOrbit pairing (dualOrbits a) ≃ WeightOrbit pairing (dualOrbits (dualBlockSwap a)) where
  toFun μ := ⟨weightDiagram μ.val, weightDiagram_mem_dualOrbit a μ.val μ.property⟩
  invFun μ := ⟨weightDiagram μ.val, by
    have h := weightDiagram_mem_dualOrbit (dualBlockSwap a) μ.val μ.property
    rw [dualBlockSwap_involutive a] at h
    exact h⟩
  left_inv μ := Subtype.ext (weightDiagram_involutive μ.val)
  right_inv μ := Subtype.ext (weightDiagram_involutive μ.val)

@[simp] theorem dualOrbitDiagram_val (a : Option Unit)
    (μ : WeightOrbit pairing (dualOrbits a)) :
    (dualOrbitDiagram a μ).val = weightDiagram μ.val := rfl

end Atlas.Chevalley.TwistedE6
