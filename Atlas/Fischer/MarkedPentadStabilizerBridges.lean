import Atlas.Fischer.MarkedPentadFrameAction
import Atlas.Fischer.MarkedFrameRayStabilizer
import Atlas.Fischer.MarkedPentadFrameCount

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def markedStandardFrame (S : Finset Omega) : MarkedPentadFrame S :=
  ⟨standardCommutingFrame,standardCommutingFrame_isFrame,fun i _ => ⟨i,rfl⟩⟩

private theorem marked_basic_image {s : ℕ} (a : Fin s ↪ Omega) :
    (fun i : Omega => distinguishedRootElement (.inl i)) '' ((Finset.univ.image a : Finset Omega) : Set Omega) =
      Set.range (fun k => distinguishedRootElement (.inl (a k))) := by
  classical
  ext x
  simp only [Set.mem_image,Finset.mem_coe,Finset.mem_image,Finset.mem_univ,true_and,
    Set.mem_range]
  constructor
  · rintro ⟨i,⟨k,rfl⟩,h⟩; exact ⟨k,h⟩
  · rintro ⟨k,h⟩; exact ⟨a k,⟨k,rfl⟩,h⟩

def markedFrameStabilizerEquiv {s : ℕ} (a : Fin s ↪ Omega) :
    MulAction.stabilizer (markedPentadPointwise (Finset.univ.image a))
      (markedStandardFrame (Finset.univ.image a)) ≃* markedFrameRayStabilizer a where
  toFun g := ⟨g.val.val, by
    refine ⟨?_,?_⟩
    · apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
      exact congrArg Subtype.val g.property
    · have h := g.val.property
      change g.val.val ∈ Subgroup.centralizer _ at h
      rw [marked_basic_image] at h
      exact h⟩
  invFun g := ⟨⟨g.val,by
    change g.val ∈ Subgroup.centralizer _
    rw [marked_basic_image]
    exact g.property.2⟩,by
      apply Subtype.ext
      exact Subgroup.mem_normalizer_iff_conj_image_eq.mp g.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem markedStandardFrame_stabilizer_order (a : Fin 5 ↪ Omega) :
    Nat.card (MulAction.stabilizer (markedPentadPointwise (Finset.univ.image a))
      (markedStandardFrame (Finset.univ.image a))) = 196608 := by
  rw [Nat.card_congr (markedFrameStabilizerEquiv a).toEquiv,markedFrameRayStabilizer_five_order]

def basicOrderedCommutingTuple {s : ℕ} (a : Fin s ↪ Omega) : OrderedCommutingTuple s :=
  ⟨basicCommutingTuple a,fun k => ⟨.inl (a k),rfl⟩,
    fun k l => standardCommutingFrame_isFrame.2.1 _ ⟨a k,rfl⟩ _ ⟨a l,rfl⟩⟩

theorem basicOrderedCommutingTuple_stabilizer {s : ℕ} (a : Fin s ↪ Omega) :
    MulAction.stabilizer rootGeneratedRayGroup (basicOrderedCommutingTuple a) =
      markedPentadPointwise (Finset.univ.image a) := by
  classical
  ext g
  rw [MulAction.mem_stabilizer_iff,mem_markedPentadPointwise_iff]
  constructor
  · intro h i hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hi
    exact congrArg (fun t : OrderedCommutingTuple s => t.val k) h
  · intro h
    apply Subtype.ext
    apply Function.Embedding.ext
    intro k
    exact h (a k) (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)

/-- The only remaining input here is the concrete fixing-switch transitivity. -/
theorem markedPentadPointwise_order_of_transitive (a : Fin 5 ↪ Omega)
    (ht : MulAction.IsPretransitive (markedPentadPointwise (Finset.univ.image a))
      (MarkedPentadFrame (Finset.univ.image a))) :
    Nat.card (markedPentadPointwise (Finset.univ.image a)) = 589824 := by
  haveI := ht
  let S := Finset.univ.image a
  have hS : S.card=5 := by
    rw [Finset.card_image_of_injective _ a.injective,Finset.card_univ,Fintype.card_fin]
  have he : MulAction.orbit (markedPentadPointwise S) (markedStandardFrame S) ≃ MarkedPentadFrame S :=
    Equiv.setCongr (MulAction.orbit_eq_univ _ _) |>.trans (Equiv.Set.univ _)
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (markedPentadPointwise S) (markedStandardFrame S))
  rw [Nat.card_prod,Nat.card_congr he,markedPentadFrame_card S hS,
    markedStandardFrame_stabilizer_order a] at hc
  exact hc.symm

end Atlas.Fischer
