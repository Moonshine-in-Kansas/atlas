import Atlas.Fischer.CountingHexacodeSupports

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Projection of the actual source code onto any three distinct columns. -/
def countingHexTripleProjection (e : Fin 3 ↪ Fin 6) :
    countingHexacode →ₗ[CountingFour] (Fin 3 → CountingFour) where
  toFun h j := h.val (e j)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem countingHexTripleProjection_injective (e : Fin 3 ↪ Fin 6) :
    Function.Injective (countingHexTripleProjection e) := by
  intro u v h
  obtain ⟨a,rfl⟩ := countingHexEquiv.surjective u
  obtain ⟨b,rfl⟩ := countingHexEquiv.surjective v
  apply congrArg countingHexEquiv
  apply codeTripleProjection_injective hexacode hexacode_isHexMDS
    (e.trans hexIndexEquiv.symm.toEmbedding)
  funext j
  have hj := congrFun h j
  change countingLetterEquiv (countingHexLocal (e j) (a.val (hexPos (e j))))=
    countingLetterEquiv (countingHexLocal (e j) (b.val (hexPos (e j)))) at hj
  exact (countingHexLocal (e j)).injective (countingLetterEquiv.injective hj)

theorem countingHexTripleProjection_bijective (e : Fin 3 ↪ Fin 6) :
    Function.Bijective (countingHexTripleProjection e) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨countingHexTripleProjection_injective e,?_⟩
  rw [← Nat.card_eq_fintype_card,countingHexacode_card]
  rw [Fintype.card_fun,Atlas.Algebra.goldenFour_card]
  decide

def countingHexTripleEquiv (e : Fin 3 ↪ Fin 6) :
    countingHexacode ≃ₗ[CountingFour] (Fin 3 → CountingFour) :=
  LinearEquiv.ofBijective (countingHexTripleProjection e)
    (countingHexTripleProjection_bijective e)

/-- Three zero coordinates force the zero source word, by retained distance four. -/
theorem countingHex_three_zeros (w : countingHexacode) (e : Fin 3 ↪ Fin 6)
    (h : ∀ j, w.val (e j)=0) : w=0 := by
  apply countingHexTripleProjection_injective e
  funext j
  exact h j

end Atlas.Fischer
