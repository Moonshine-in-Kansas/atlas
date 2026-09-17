import Atlas.Combinatorics.SteinerCounting

noncomputable section
namespace Atlas.Combinatorics
open Finset
variable {α : Type*} [Fintype α]
variable [DecidableEq α]

abbrev PointComplement (a : α) := {x : α // x ≠ a}
local instance (a : α) : Fintype (PointComplement a) := Fintype.ofFinite _

def complementBlockLift (a : α) (B : Finset (PointComplement a)) : Finset α :=
  B.map (Function.Embedding.subtype _)

@[simp] theorem complementBlockLift_not_mem (a : α) (B : Finset (PointComplement a)) :
    a ∉ complementBlockLift a B := by
  rintro h
  obtain ⟨x,_,hx⟩ := mem_map.mp h
  exact x.prop hx

@[simp] theorem complementBlockLift_card (a : α) (B : Finset (PointComplement a)) :
    (complementBlockLift a B).card = B.card := card_map _

def derivedBlocks (blocks : Finset (Finset α)) (a : α) : Finset (Finset (PointComplement a)) := by
  classical
  exact univ.filter (fun B => insert a (complementBlockLift a B) ∈ blocks)

@[simp] theorem derivedBlocks_mem (blocks : Finset (Finset α)) (a : α)
    (B : Finset (PointComplement a)) :
    B ∈ derivedBlocks blocks a ↔ insert a (complementBlockLift a B) ∈ blocks := by
  classical
  simp [derivedBlocks]

theorem derivedBlocks_size (blocks : Finset (Finset α)) (a : α) (k : ℕ)
    (sizes : ∀ B ∈ blocks, B.card = k + 1) (B : Finset (PointComplement a))
    (hB : B ∈ derivedBlocks blocks a) : B.card = k := by
  have h := sizes _ ((derivedBlocks_mem blocks a B).mp hB)
  simp only [card_insert_of_notMem (complementBlockLift_not_mem a B), complementBlockLift_card] at h
  omega

def complementBlockRestrict (a : α) (O : Finset α) : Finset (PointComplement a) := by
  classical
  exact O.subtype (fun x => x ≠ a)

theorem complementBlock_restore (a : α) (O : Finset α) (ha : a ∈ O) :
    insert a (complementBlockLift a (complementBlockRestrict a O)) = O := by
  classical
  ext x
  simp only [complementBlockLift, complementBlockRestrict, subtype_map, mem_insert, mem_filter]
  constructor
  · rintro (rfl | ⟨hx,_⟩)
    · exact ha
    · exact hx
  · intro hx
    by_cases h : x = a
    · exact Or.inl h
    · exact Or.inr ⟨hx,h⟩

theorem derived_steiner (blocks : Finset (Finset α)) (a : α) (t : ℕ)
    (unique : ∀ T : Finset α, T.card = t + 1 → ∃! B, B ∈ blocks ∧ T ⊆ B)
    (T : Finset (PointComplement a)) (hT : T.card = t) :
    ∃! B : Finset (PointComplement a), B ∈ derivedBlocks blocks a ∧ T ⊆ B := by
  classical
  obtain ⟨O,⟨hO,hTO⟩,huniq⟩ := unique (insert a (complementBlockLift a T)) (by simp [hT])
  have ha : a ∈ O := hTO (mem_insert_self _ _)
  refine ⟨complementBlockRestrict a O, ⟨?_,?_⟩,?_⟩
  · rw [derivedBlocks_mem, complementBlock_restore a O ha]
    exact hO
  · intro x hx
    change x ∈ O.subtype _
    rw [mem_subtype]
    exact hTO (mem_insert_of_mem (mem_map.mpr ⟨x,hx,rfl⟩))
  · intro B hB
    have he : insert a (complementBlockLift a B) = O := huniq _
      ⟨(derivedBlocks_mem blocks a B).mp hB.1, insert_subset_insert a (map_subset_map.mpr hB.2)⟩
    ext x
    have hh := congrArg (fun P : Finset α => x.val ∈ P) he
    simpa [complementBlockRestrict, complementBlockLift, x.prop] using Iff.of_eq hh

end Atlas.Combinatorics
