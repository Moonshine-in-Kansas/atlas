import Atlas.LinearGroups.Unitary.CoordinateBlocks
import Atlas.LinearGroups.Unitary.FourCompression
import Atlas.LinearGroups.Unitary.SupportReduction

/-! Support reduction using actual four-coordinate special-unitary blocks. -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n k : ℕ}

/-- If at least four coordinates are nonzero, a generated SU₄ block decreases
support, even when the norm on those four coordinates vanishes. -/
theorem exists_generated_reduce_support_four (hdeg : Module.finrank F K = 2)
    (hfour : transvectionGenerated hdeg (n := 4) = ⊤) (v : Fin (4+k) → K) (hv : 4 ≤ (vectorSupport v).card) :
    ∃ g : SU F K (4+k) hdeg, g ∈ transvectionGenerated hdeg ∧
      (vectorSupport (g.val *ᵥ v)).card < (vectorSupport v).card := by
  classical
  obtain ⟨s, hsub, hs⟩ := Finset.exists_subset_card_eq hv
  let e : s ≃ Fin 4 := s.equivFinOfCardEq hs
  let I : Fin 4 ↪ Fin (4+k) := e.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hI : ∀ i, v (I i) ≠ 0 := fun i =>
    (mem_vectorSupport v _).mp (hsub (e.symm i).property)
  obtain ⟨g,hg⟩ := exists_special_compress_four hdeg (v ∘ I)
  have hggen : g ∈ transvectionGenerated hdeg := by
    rw [hfour]; trivial
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
  have hzero : (G.val *ᵥ v) (I 3) = 0 :=
    (coordinateBlockHom_apply_inside hdeg I g v 3).trans hg
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsubset, ?_⟩
  intro heq
  have hi := (mem_vectorSupport v (I 3)).mpr (hI 3)
  rw [← heq] at hi
  exact (mem_vectorSupport (G.val *ᵥ v) (I 3)).mp hi hzero

/-- Finite support descent gives a generated transformation into some three-coordinate subspace. -/
theorem exists_generated_sparse_four (hdeg : Module.finrank F K = 2)
    (hfour : transvectionGenerated hdeg (n := 4) = ⊤) (v : Fin (4+k) → K) :
    ∃ g : SU F K (4+k) hdeg, g ∈ transvectionGenerated hdeg ∧
      (vectorSupport (g.val *ᵥ v)).card ≤ 3 := by
  classical
  generalize hm : (vectorSupport v).card = m
  induction m using Nat.strong_induction_on generalizing v with
  | h m ih =>
    by_cases hsmall : m ≤ 3
    · refine ⟨1, (transvectionGenerated hdeg).one_mem, ?_⟩
      simpa only [show (1 : SU F K (4+k) hdeg).val = 1 from rfl, one_mulVec, hm] using hsmall
    · obtain ⟨g,hg,hlt⟩ := exists_generated_reduce_support_four hdeg hfour v (by omega)
      obtain ⟨h,hh,hsparse⟩ := ih (vectorSupport (g.val *ᵥ v)).card (by omega) (g.val *ᵥ v) rfl
      refine ⟨h*g, (transvectionGenerated hdeg).mul_mem hh hg, ?_⟩
      change (vectorSupport ((h.val*g.val) *ᵥ v)).card ≤ 3
      rwa [← mulVec_mulVec]
end Atlas.Unitary
