import Atlas.Fischer.OctadicRootCoordinates
import Atlas.Fischer.OctadAffineEvaluations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- Count the actual nonconstant shortened words by deleting 0 and X. -/
theorem octadShortenedHyperplane_card (O : Octad) :
    Fintype.card (OctadShortenedHyperplane O) = 30 := by
  classical
  have hc : Fintype.card (octadShortenedCode O) = 32 := by
    simpa only [Nat.card_eq_fintype_card] using octadShortenedCode_card O
  have h := Fintype.card_of_subtype ({0,octadShortenedOne O}ᶜ : Finset (octadShortenedCode O))
    (p := fun b => b ≠ 0 ∧ b ≠ octadShortenedOne O) (by intro b; simp)
  rw [h,Finset.card_compl,hc]
  simp [Ne.symm (octadShortenedOne_ne_zero O)]

theorem octadShortenedHyperplane_natCard (O : Octad) :
    Nat.card (OctadShortenedHyperplane O) = 30 := by
  classical
  rw [Nat.card_eq_fintype_card,octadShortenedHyperplane_card]

theorem octadEvaluation_surjective (O : Octad) (i : OctadExterior O) :
    Function.Surjective (octadEvaluation O i) := by
  intro a
  exact ⟨a • octadShortenedOne O, by simp⟩

theorem octadEvaluation_fiber_card (O : Octad) (i : OctadExterior O) (a : Bit) :
    Fintype.card {b : octadShortenedCode O // octadEvaluation O i b = a} = 16 := by
  classical
  have hk : Module.finrank Bit (octadEvaluation O i).ker = 4 := by
    have h := (octadEvaluation O i).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (octadEvaluation_surjective O i),finrank_top,
      Module.finrank_self,octadShortenedCode_finrank] at h
    omega
  have h := Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective
    (f := (octadEvaluation O i).toAddMonoidHom) (octadEvaluation_surjective O i) a)
  change Nat.card {b : octadShortenedCode O // octadEvaluation O i b = a} =
    Nat.card (octadEvaluation O i).ker at h
  have hc : Nat.card (octadEvaluation O i).ker = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := Bit),hk]
    simp [Bit]
  rw [hc] at h
  simpa only [Nat.card_eq_fintype_card] using h

/-- Each retained exterior point is on exactly fifteen actual affine hyperplanes. -/
theorem octadShortenedHyperplane_through_point (O : Octad) (i : OctadExterior O) :
    Fintype.card {b : OctadShortenedHyperplane O // b.val.val.val i.val = 1} = 15 := by
  classical
  let F := {b : octadShortenedCode O // octadEvaluation O i b = 1}
  let x : F := ⟨octadShortenedOne O,octadEvaluation_one O i⟩
  let e : {b : OctadShortenedHyperplane O // b.val.val.val i.val = 1} ≃
      {b : F // b ≠ x} :=
    { toFun := fun b => ⟨⟨b.val.val,b.prop⟩, fun h => b.val.prop.2 (congrArg Subtype.val h)⟩
      invFun := fun b => ⟨⟨b.val.val, ⟨by
        intro h
        have hh := b.val.prop
        rw [h,map_zero] at hh
        exact zero_ne_one hh,
        fun h => b.prop (Subtype.ext h)⟩⟩,b.val.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  have h := Fintype.card_subtype_compl (fun b : F => b = x)
  rw [Fintype.card_subtype_eq] at h
  have hc : Fintype.card F = 16 := octadEvaluation_fiber_card O i 1
  rw [h,hc]

end Atlas.Fischer
