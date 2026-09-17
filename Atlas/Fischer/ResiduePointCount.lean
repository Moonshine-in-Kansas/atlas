import Atlas.Fischer.ResidueModels
import Atlas.Fischer.ResidueCentralizerOrder

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def residuePointExtensionEquiv (S : Finset Omega) :
    ResiduePoint S ≃ CommutingExtension (basicCommutingTuple (residueCoordinateEmbedding S)) := by
  classical
  apply Equiv.subtypeEquiv (Equiv.refl rootGeneratedRayGroup)
  intro x
  change (x ∈ Set.range distinguishedRootElement ∧ x ∉ residueBasicSet S ∧
    ∀ i ∈ S, Commute (distinguishedRootElement (.inl i)) x) ↔
    (x ∈ Set.range distinguishedRootElement ∧ ∀ k,
      x ≠ distinguishedRootElement (.inl (residueCoordinateEmbedding S k)) ∧
      Commute (distinguishedRootElement (.inl (residueCoordinateEmbedding S k))) x)
  apply and_congr_right
  intro hx
  constructor
  · rintro ⟨hne,hc⟩ k
    have hk : residueCoordinateEmbedding S k ∈ S := by
      simpa only [residueCoordinateEmbedding_image] using
        (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩ :
          residueCoordinateEmbedding S k ∈ Finset.univ.image (residueCoordinateEmbedding S))
    exact ⟨fun he => hne ⟨_,hk,he.symm⟩, hc _ hk⟩
  · intro h
    constructor
    · rintro ⟨i,hi,he⟩
      rw [← residueCoordinateEmbedding_image S] at hi
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
      exact (h k).1 he.symm
    · intro i hi
      rw [← residueCoordinateEmbedding_image S] at hi
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
      exact (h k).2

/-- Residue points remain original distinguished elements, counted before quotienting. -/
theorem residuePoint_card (S : Finset Omega) (hS : S.card ≤ 5) :
    Nat.card (ResiduePoint S) = ![306936,31671,3510,693,180,51] ⟨S.card,by omega⟩ := by
  rw [Nat.card_congr (residuePointExtensionEquiv S)]
  exact commutingExtension_card hS _
    (basicOrderedCommutingTuple (residueCoordinateEmbedding S)).property.1
    (basicOrderedCommutingTuple (residueCoordinateEmbedding S)).property.2

theorem residuePoint_singleton_card (S : Finset Omega) (hS : S.card = 1) :
    Nat.card (ResiduePoint S) = 31671 := by
  rw [residuePoint_card S (by omega)]
  simp [hS]

theorem residuePoint_pair_card (S : Finset Omega) (hS : S.card = 2) :
    Nat.card (ResiduePoint S) = 3510 := by
  rw [residuePoint_card S (by omega)]
  simp [hS]

end Atlas.Fischer
