import Atlas.Fischer.OctadParkerSections
import Atlas.Fischer.ParkerMonomialData

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Fischer
open Atlas.Codes

 theorem parkerCodeEquiv_at_image (e : ParkerStandardGroup) (c : golay) (i : Omega) :
    (parkerCodeEquiv (parkerStandardProjection e) c).val
      ((parkerStandardProjection e).val i) = c.val i := by
  change c.val ((parkerStandardProjection e).val.symm ((parkerStandardProjection e).val i)) = _
  rw [Equiv.symm_apply_apply]

theorem parkerCodeEquiv_shortened_iff (e : ParkerStandardGroup) (O : Octad) (c : golay) :
    parkerCodeEquiv (parkerStandardProjection e) c ∈
      octadShortenedCode (parkerOctadAction e O) ↔ c ∈ octadShortenedCode O := by
  classical
  have hm (i : Omega) : (parkerStandardProjection e).val i ∈ (parkerOctadAction e O).val ↔
      i ∈ O.val := by simp [parkerOctadAction,permuteBlock]
  rw [mem_octadShortenedCode,mem_octadShortenedCode]
  constructor
  · intro h i hi
    rw [← parkerCodeEquiv_at_image e c i]
    exact h _ ((hm i).mpr hi)
  · intro h j hj
    obtain ⟨i,rfl⟩ := (parkerStandardProjection e).val.surjective j
    rw [parkerCodeEquiv_at_image]
    exact h i ((hm i).mp hj)

/-- Restriction of the actual induced Golay permutation to shortened codes. -/
noncomputable def octadShortenedTransport (e : ParkerStandardGroup) (O : Octad) :
    octadShortenedCode O ≃ₗ[Bit] octadShortenedCode (parkerOctadAction e O) where
  toFun c := ⟨parkerCodeEquiv (parkerStandardProjection e) c.val,
    (parkerCodeEquiv_shortened_iff e O c.val).mpr c.property⟩
  invFun d := ⟨(parkerCodeEquiv (parkerStandardProjection e)).symm d.val, by
    apply (parkerCodeEquiv_shortened_iff e O _).mp
    simpa only [LinearEquiv.apply_symm_apply] using d.property⟩
  left_inv c := Subtype.ext ((parkerCodeEquiv (parkerStandardProjection e)).symm_apply_apply c.val)
  right_inv d := Subtype.ext ((parkerCodeEquiv (parkerStandardProjection e)).apply_symm_apply d.val)
  map_add' c d := Subtype.ext (map_add _ _ _)
  map_smul' r c := Subtype.ext (map_smul _ _ _)

@[simp] theorem octadShortenedTransport_val (e : ParkerStandardGroup) (O : Octad)
    (c : octadShortenedCode O) :
    (octadShortenedTransport e O c).val = parkerCodeEquiv (parkerStandardProjection e) c.val := rfl

theorem octadShortenedTransport_one (e : ParkerStandardGroup) (O : Octad) :
    octadShortenedTransport e O (octadShortenedOne O) =
      octadShortenedOne (parkerOctadAction e O) := by
  apply Subtype.ext
  change parkerCodeEquiv (parkerStandardProjection e) (golayOne+octadWord O) =
    golayOne+octadWord (parkerOctadAction e O)
  rw [map_add,parkerCodeEquiv_golayOne,parkerOctadWord_action]

/-- Pullback of actual binary characters, with explicit left-action convention. -/
noncomputable def octadCharacterPullback (e : ParkerStandardGroup) (O : Octad) :
    Module.Dual Bit (octadShortenedCode (parkerOctadAction e O)) ≃ₗ[Bit]
      Module.Dual Bit (octadShortenedCode O) where
  toFun χ := χ.comp (octadShortenedTransport e O).toLinearMap
  invFun χ := χ.comp (octadShortenedTransport e O).symm.toLinearMap
  left_inv χ := by ext a; simp
  right_inv χ := by ext a; simp
  map_add' χ ψ := by ext a; rfl
  map_smul' r χ := by ext a; rfl

@[simp] theorem octadCharacterPullback_apply (e : ParkerStandardGroup) (O : Octad)
    (χ : Module.Dual Bit (octadShortenedCode (parkerOctadAction e O)))
    (c : octadShortenedCode O) : octadCharacterPullback e O χ c = χ (octadShortenedTransport e O c) := rfl

theorem octadCharacterPullback_constant (e : ParkerStandardGroup) (O : Octad)
    (χ : Module.Dual Bit (octadShortenedCode (parkerOctadAction e O))) :
    octadCharacterPullback e O χ (octadShortenedOne O) =
      χ (octadShortenedOne (parkerOctadAction e O)) := by
  rw [octadCharacterPullback_apply,octadShortenedTransport_one]

end Atlas.Fischer
