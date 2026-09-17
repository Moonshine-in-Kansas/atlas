import Atlas.Fischer.CommutingExtensionModels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def commutingExtensionConjEquiv {s : ℕ} (t u : Fin s ↪ rootGeneratedRayGroup)
    (g : rootGeneratedRayGroup) (hg : ∀ k, MulAut.conj g (t k) = u k) :
    CommutingExtension t ≃ CommutingExtension u := by
  apply Equiv.subtypeEquiv (MulAut.conj g).toEquiv
  intro x
  have hD : x ∈ Set.range distinguishedRootElement ↔
      MulAut.conj g x ∈ Set.range distinguishedRootElement := by
    let i : ReflectingRootParameter := .inl (Classical.choice inferInstance)
    rw [distinguishedRootClass_isConj_iff i, distinguishedRootClass_isConj_iff i]
    exact ⟨fun h => h.trans (isConj_iff.mpr ⟨g,rfl⟩),
      fun h => h.trans (isConj_iff.mpr ⟨g⁻¹,by simp [MulAut.conj_apply,mul_assoc]⟩)⟩
  change (x ∈ Set.range distinguishedRootElement ∧ ∀ k, x ≠ t k ∧ Commute (t k) x) ↔
    (MulAut.conj g x ∈ Set.range distinguishedRootElement ∧ ∀ k, MulAut.conj g x ≠ u k ∧ Commute (u k) (MulAut.conj g x))
  rw [hD]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  rw [← hg k]
  constructor
  · rintro ⟨hne,hc⟩
    exact ⟨fun h => hne ((MulAut.conj g).injective h),hc.map (MulAut.conj g)⟩
  · rintro ⟨hne,hc⟩
    refine ⟨fun h => hne (congrArg (MulAut.conj g) h),?_⟩
    apply (MulAut.conj g).injective
    simpa only [map_mul] using hc.eq

/-- Common-extension numbers for every actual ordered commuting tuple of length
at most five, transferred from the independently counted marked supports. -/
theorem commutingExtension_card {s : ℕ} (hs : s ≤ 5)
    (t : Fin s ↪ rootGeneratedRayGroup)
    (ht : ∀ k, t k ∈ Set.range distinguishedRootElement)
    (hc : ∀ k l, Commute (t k) (t l)) :
    Nat.card (CommutingExtension t) = ![306936,31671,3510,693,180,51] ⟨s,by omega⟩ := by
  classical
  obtain ⟨g,a,hg⟩ := commutingTuple_into_standard t ht hc
  rw [Nat.card_congr (commutingExtensionConjEquiv t (basicCommutingTuple a) g hg),
    ← Nat.card_congr (markedBasicExtensionGroupEquiv a),
    ← markedBasicExtensionRay_card]
  apply markedBasicExtensionRay_card_values
  rw [Finset.card_image_of_injective _ a.injective, Finset.card_univ, Fintype.card_fin]

end Atlas.Fischer
