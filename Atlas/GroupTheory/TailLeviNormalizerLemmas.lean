import Atlas.GroupTheory.OrderedSubgroupCollection

/-!
Source-only helpers for the Levi normalization repair. All group algebra and
finite-join simplification below take place in an abstract group. This module
does not import Ree, Albert, or the separately audited TailNormalizerLemmas.
No compilation, proof checking, audit, or resource measurement was performed.
-/

namespace Atlas.GroupTheory.TailLeviNormalizer

variable {G : Type*} [Group G]

/-- A commuting right factor does not change conjugation of the given element. -/
theorem conjugate_mul_of_commute (x c y : G) (hc : Commute c y) :
    (x * c) * y * (x * c)⁻¹ = x * y * x⁻¹ := by
  calc
    (x * c) * y * (x * c)⁻¹ = x * (c * y) * c⁻¹ * x⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    _ = x * (y * c) * c⁻¹ * x⁻¹ := by rw [hc.eq]
    _ = x * y * x⁻¹ := by
      simp only [mul_assoc, mul_inv_cancel_left]

/-- If T normalizes a range and p normalizes T, T normalizes the conjugated range. -/
theorem normalizes_conjugated_range {A : Type*} [Group A]
    (T : Subgroup G) (f : A →* G) (p : G)
    (hp : p ∈ Subgroup.normalizer (T : Set G))
    (hf : T ≤ Subgroup.normalizer (f.range : Set G)) :
    T ≤ Subgroup.normalizer
      (((MulAut.conj p).toMonoidHom.comp f).range : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro t ht x ⟨a, rfl⟩
  let s : G := p⁻¹ * t * p
  have hs : s ∈ T := (Subgroup.mem_normalizer_iff''.mp hp t).mp ht
  obtain ⟨b, hb⟩ :=
    (Subgroup.mem_normalizer_iff.mp (hf hs) (f a)).mp ⟨a, rfl⟩
  refine ⟨b, ?_⟩
  change p * f b * p⁻¹ = t * (p * f a * p⁻¹) * t⁻¹
  rw [hb]
  dsimp only [s]
  simp only [mul_inv_rev, inv_inv, mul_assoc,
    mul_inv_cancel_left, mul_inv_cancel, mul_one]

/-- Combine two normalizer inclusions without eliminating subgroup equalities. -/
theorem le_normalizer_sup (T H K : Subgroup G)
    (hH : T ≤ Subgroup.normalizer (H : Set G))
    (hK : T ≤ Subgroup.normalizer (K : Set G)) :
    T ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  (le_inf hH hK).trans (H.normalizer_inf_normalizer_le_normalizer_sup K)

/-- Seven literal subgroup inclusions suffice. The terminal bottom is removed
in the abstract lattice, so there is no singleton-normalizer base case. -/
theorem le_normalizer_subgroupListJoin_seven
    (T H₀ H₁ H₂ H₃ H₄ H₅ H₆ : Subgroup G)
    (h₀ : T ≤ Subgroup.normalizer (H₀ : Set G))
    (h₁ : T ≤ Subgroup.normalizer (H₁ : Set G))
    (h₂ : T ≤ Subgroup.normalizer (H₂ : Set G))
    (h₃ : T ≤ Subgroup.normalizer (H₃ : Set G))
    (h₄ : T ≤ Subgroup.normalizer (H₄ : Set G))
    (h₅ : T ≤ Subgroup.normalizer (H₅ : Set G))
    (h₆ : T ≤ Subgroup.normalizer (H₆ : Set G)) :
    T ≤ Subgroup.normalizer
      (subgroupListJoin [H₀, H₁, H₂, H₃, H₄, H₅, H₆] : Set G) := by
  have h : T ≤ Subgroup.normalizer
      ((H₀ ⊔ (H₁ ⊔ (H₂ ⊔ (H₃ ⊔ (H₄ ⊔ (H₅ ⊔ H₆))))) : Subgroup G) : Set G) :=
    le_normalizer_sup T H₀ _ h₀
      (le_normalizer_sup T H₁ _ h₁
        (le_normalizer_sup T H₂ _ h₂
          (le_normalizer_sup T H₃ _ h₃
            (le_normalizer_sup T H₄ _ h₄
              (le_normalizer_sup T H₅ H₆ h₅ h₆)))))
  simpa only [subgroupListJoin, sup_bot_eq] using h

end Atlas.GroupTheory.TailLeviNormalizer
