import Atlas.LinearGroups.Unitary.CoordinateBlocks
import Atlas.LinearGroups.Unitary.ThreeCompression
import Atlas.LinearGroups.Unitary.GenerationThreeComplete

/-! Support reduction using actual three-coordinate special-unitary blocks. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n k : ℕ}

/-- Actual nonzero coordinates, used only as the termination measure. -/
def vectorSupport (v : Fin n → K) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => v i ≠ 0)

@[simp] theorem mem_vectorSupport (v : Fin n → K) (i : Fin n) :
    i ∈ vectorSupport v ↔ v i ≠ 0 := by
  classical
  simp [vectorSupport]

/-- If at least three coordinates are nonzero, a generated SU₃ block decreases
support, even when the norm on those three coordinates vanishes. -/
theorem exists_generated_reduce_support (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) (v : Fin (3+k) → K) (hv : 3 ≤ (vectorSupport v).card) :
    ∃ g : SU F K (3+k) hdeg, g ∈ transvectionGenerated hdeg ∧
      (vectorSupport (g.val *ᵥ v)).card < (vectorSupport v).card := by
  classical
  obtain ⟨s, hsub, hs⟩ := Finset.exists_subset_card_eq hv
  let e : s ≃ Fin 3 := s.equivFinOfCardEq hs
  let I : Fin 3 ↪ Fin (3+k) := e.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hI : ∀ i, v (I i) ≠ 0 := fun i =>
    (mem_vectorSupport v _).mp (hsub (e.symm i).property)
  obtain ⟨g,hg⟩ := exists_special_compress_three hdeg (v ∘ I)
  have hggen : g ∈ transvectionGenerated hdeg := by
    rw [transvectionGenerated_three_eq_top hdeg hq]; trivial
  let G := coordinateBlockHom hdeg I g
  refine ⟨G, coordinateBlockHom_generated hdeg I g hggen, ?_⟩
  have hsubset : vectorSupport (G.val *ᵥ v) ⊆ vectorSupport v := by
    intro i hi
    apply (mem_vectorSupport v i).mpr
    by_cases hiI : i ∈ Set.range I
    · obtain ⟨j,rfl⟩ := hiI
      exact hI j
    · have he := coordinateBlockHom_apply_outside hdeg I g v i hiI
      exact he ▸ (mem_vectorSupport (G.val *ᵥ v) i).mp hi
  have hzero : (G.val *ᵥ v) (I 2) = 0 :=
    (coordinateBlockHom_apply_inside hdeg I g v 2).trans hg
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsubset, ?_⟩
  intro heq
  have hi := (mem_vectorSupport v (I 2)).mpr (hI 2)
  rw [← heq] at hi
  exact (mem_vectorSupport (G.val *ᵥ v) (I 2)).mp hi hzero

/-- Finite support descent gives a generated transformation into some coordinate plane. -/
theorem exists_generated_sparse (hdeg : Module.finrank F K = 2)
    (hq : 2 < Nat.card F) (v : Fin (3+k) → K) :
    ∃ g : SU F K (3+k) hdeg, g ∈ transvectionGenerated hdeg ∧
      (vectorSupport (g.val *ᵥ v)).card ≤ 2 := by
  classical
  generalize hm : (vectorSupport v).card = m
  induction m using Nat.strong_induction_on generalizing v with
  | h m ih =>
    by_cases hsmall : m ≤ 2
    · refine ⟨1, (transvectionGenerated hdeg).one_mem, ?_⟩
      simpa only [show (1 : SU F K (3+k) hdeg).val = 1 from rfl, one_mulVec, hm] using hsmall
    · obtain ⟨g,hg,hlt⟩ := exists_generated_reduce_support hdeg hq v (by omega)
      obtain ⟨h,hh,hsparse⟩ := ih (vectorSupport (g.val *ᵥ v)).card (by omega) (g.val *ᵥ v) rfl
      refine ⟨h*g, (transvectionGenerated hdeg).mul_mem hh hg, ?_⟩
      change (vectorSupport ((h.val*g.val) *ᵥ v)).card ≤ 2
      rwa [← mulVec_mulVec]
end Atlas.Unitary
