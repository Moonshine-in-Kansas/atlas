import Atlas.LinearGroups.Chevalley.ModelDegreeOrder
import Atlas.LinearGroups.Chevalley.ModelSimplicityIffGood
import Mathlib.FieldTheory.Finite.GaloisField

/-! Concrete construction and prime-power endpoints for the uniform model.
This source candidate awaits the uniform degree and exact-exception modules.
It asserts no Curtis–Tits theorem or comparison with an older realization. -/
noncomputable section
universe u
namespace Atlas.Chevalley

/-- Properties of the specified root-operator groups. The fields below are
conclusions assembled after their independent proofs, not input assumptions
used to construct a group. The selected cover is kept distinct from Model. -/
structure Construction (Φ : RootType) (K : Type*) [Field K] : Prop where
  finite : Finite (Model Φ K)
  cover_finite : Finite (SelectedWeightCompanion Φ K)
  cover_order : Nat.card (SelectedWeightCompanion Φ K) =
    Φ.orderPolynomial (Nat.card K)
  center_kernel : Subgroup.center (SelectedWeightCompanion Φ K) =
    (selectedWeightCompanionRho Φ K).ker
  center_order : Nat.card (Subgroup.center (SelectedWeightCompanion Φ K)) =
    Φ.centerFactor (Nat.card K)
  quotient : Nonempty
    (SelectedWeightCompanion Φ K ⧸ Subgroup.center (SelectedWeightCompanion Φ K) ≃*
      Model Φ K)
  order : Nat.card (Model Φ K) =
    Φ.orderPolynomial (Nat.card K) / Φ.centerFactor (Nat.card K)
  simple_iff : IsSimpleGroup (Model Φ K) ↔ Φ.Good (Nat.card K)
  noncommutative : ¬ IsMulCommutative (Model Φ K)

theorem construction (Φ : RootType) (K : Type*) [Field K] [Finite K] :
    Construction Φ K := by
  letI : Fintype K := Fintype.ofFinite K
  exact {
    finite := inferInstance
    cover_finite := inferInstance
    cover_order := selectedWeightCompanion_card_eq_orderPolynomial Φ K
    center_kernel := selectedWeightCompanion_center_eq_rhoKernel Φ K
    center_order := by
      simpa only [Nat.card_eq_fintype_card (α := K)] using
        selectedWeightCompanion_center_card Φ K
    quotient := ⟨selectedWeightCompanionCenterQuotientAdjointEquiv Φ K⟩
    order := model_card_eq_orderPolynomial_div_centerFactor Φ K
    simple_iff := model_isSimpleGroup_iff_good Φ K
    noncommutative := model_not_commutative Φ K }

/-- The construction exists over a field of each prime-power cardinality,
including the nonsimple parameters; the carrier is never replaced there. -/
theorem construction_prime_power (Φ : RootType) (p f : ℕ)
    (hp : p.Prime) (hf : 1 ≤ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = p ^ f ∧ Construction Φ K := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f (by omega), construction Φ (GaloisField p f)⟩

/-- The existence witness is the actual root-operator model, with its
finite-field parameter and concrete identification retained explicitly. -/
theorem exists_model (Φ : RootType) (K : Type u) [Field K] [Finite K]
    (hgood : Φ.Good (Nat.card K)) :
    ∃ (G : Type u) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      ¬ IsMulCommutative G ∧
      Nat.card G = Φ.orderPolynomial (Nat.card K) / Φ.centerFactor (Nat.card K) ∧
      Nonempty (G ≃* Model Φ K) :=
  ⟨Model Φ K, inferInstance, inferInstance,
    (model_isSimpleGroup_iff_good Φ K).mpr hgood,
    model_not_commutative Φ K,
    model_card_eq_orderPolynomial_div_centerFactor Φ K, ⟨MulEquiv.refl _⟩⟩

/-- A simple-group witness for every good prime-power parameter. The order
and simplicity refer to the same witness, namely Model over a Galois field. -/
theorem exists_model_prime_power (Φ : RootType) (p f : ℕ)
    (hp : p.Prime) (hf : 1 ≤ f) (hgood : Φ.Good (p ^ f)) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      ¬ IsMulCommutative G ∧
      Nat.card G = Φ.orderPolynomial (p ^ f) / Φ.centerFactor (p ^ f) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega : f ≠ 0)
  refine ⟨Model Φ (GaloisField p f), inferInstance, inferInstance, ?_,
    model_not_commutative Φ (GaloisField p f), ?_⟩
  · apply (model_isSimpleGroup_iff_good Φ (GaloisField p f)).mpr
    simpa only [hc] using hgood
  · rw [model_card_eq_orderPolynomial_div_centerFactor, hc]

end Atlas.Chevalley
