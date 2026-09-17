import Atlas.Fischer.MathieuOctadInsideFull
import Atlas.Fischer.OctadCharacterTranslations

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

def mathieuOctadLinearHom (O : Octad) :
    MathieuOctadStabilizer O →* (BinaryFourSpace ≃ₗ[Bit] BinaryFourSpace) :=
  AffineEquiv.linearHom.comp (mathieuOctadAffineHom O)

/-- The actual subgroup inducing translations on the marked affine complement. -/
def mathieuOctadTranslations (O : Octad) : Subgroup (MathieuOctadStabilizer O) :=
  (mathieuOctadLinearHom O).ker

instance (O : Octad) : (mathieuOctadTranslations O).Normal := inferInstanceAs
  (mathieuOctadLinearHom O).ker.Normal

theorem mathieuOctadLinearHom_surjective (O : Octad) :
    Function.Surjective (mathieuOctadLinearHom O) := by
  intro a
  obtain ⟨g,hg⟩ := mathieuOctadAffineHom_surjective O a.toAffineEquiv
  exact ⟨g,congrArg AffineEquiv.linear hg⟩

theorem mathieuOctadTranslations_order (O : Octad) : Nat.card (mathieuOctadTranslations O)=16 := by
  have he := (mathieuOctadTranslations O).card_mul_index
  have hi : (mathieuOctadTranslations O).index=20160 := by
    rw [mathieuOctadTranslations,Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr (mathieuOctadLinearHom_surjective O),Subgroup.card_top,
      binaryFourLinear_order]
  rw [hi,mathieuOctadStabilizer_order] at he
  omega

/-- The affine translations are exactly the pointwise octad kernel. -/
theorem mathieuOctadTranslations_eq_pointwise (O : Octad) :
    mathieuOctadTranslations O=mathieuOctadPointwise O := by
  let T := mathieuOctadTranslations O
  let f := mathieuOctadAlternatingHom O
  letI : IsSimpleGroup (alternatingGroup (OctadInterior O)) :=
    alternatingGroup.isSimpleGroup (by rw [octadInterior_card]; decide)
  haveI : (T.map f).Normal := Subgroup.Normal.map inferInstance f
    (mathieuOctadAlternating_surjective O)
  have hm : T.map f=⊥ := by
    rcases (inferInstance : (T.map f).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hd := T.card_map_dvd f
      rw [h,Subgroup.card_top,octadAlternating_card,mathieuOctadTranslations_order] at hd
      norm_num at hd
  have hle : T ≤ mathieuOctadPointwise O := by
    intro g hg
    have hmem : f g ∈ T.map f := ⟨g,hg,rfl⟩
    rw [hm] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [mathieuOctadPointwise_order,mathieuOctadTranslations_order])

/-- Every character translation extends to an actual Mathieu coordinate permutation. -/
def mathieuOctadCharacterLift (O : Octad) (t : OctadTranslationSpace O) : MathieuOctadStabilizer O :=
  (mathieuOctadAffineEquivalence O).symm
    (AffineEquiv.constVAdd Bit BinaryFourSpace (octadDirectionCoordinates O t))

theorem mathieuOctadCharacterLift_mem (O : Octad) (t : OctadTranslationSpace O) :
    mathieuOctadCharacterLift O t ∈ mathieuOctadPointwise O := by
  rw [← mathieuOctadTranslations_eq_pointwise]
  change (mathieuOctadAffineHom O (mathieuOctadCharacterLift O t)).linear=1
  change ((mathieuOctadAffineEquivalence O)
    ((mathieuOctadAffineEquivalence O).symm _)).linear=1
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem mathieuOctadCharacterLift_exterior (O : Octad) (t : OctadTranslationSpace O) :
    mathieuOctadExteriorPerm O (mathieuOctadCharacterLift O t)=octadCharacterTranslation O t := by
  apply Equiv.ext
  intro i
  apply (octadExteriorCoordinates O).injective
  have h := congrArg (fun a : BinaryFourSpace ≃ᵃ[Bit] BinaryFourSpace =>
    a (octadExteriorCoordinates O i))
    ((mathieuOctadAffineEquivalence O).apply_symm_apply
      (AffineEquiv.constVAdd Bit BinaryFourSpace (octadDirectionCoordinates O t)))
  rw [octadCharacterTranslation_coordinates]
  change mathieuOctadCoordinatePerm O (mathieuOctadCharacterLift O t)
    (octadExteriorCoordinates O i) =
      octadDirectionCoordinates O t + octadExteriorCoordinates O i at h
  simpa only [mathieuOctadCoordinatePerm, Equiv.trans_apply,
    Equiv.symm_apply_apply, add_comm] using h

/-- The actual pointwise octad subgroup acts regularly on its sixteen exterior points. -/
theorem mathieuOctadPointwise_regular (O : Octad) (i j : OctadExterior O) :
    ∃! g : mathieuOctadPointwise O, mathieuOctadExteriorPerm O g.val i=j := by
  let f : mathieuOctadPointwise O → OctadExterior O :=
    fun g => mathieuOctadExteriorPerm O g.val i
  have hs : Function.Surjective f := by
    intro k
    obtain ⟨t,ht,_⟩ := octadCharacterTranslation_regular O i k
    refine ⟨⟨mathieuOctadCharacterLift O t,mathieuOctadCharacterLift_mem O t⟩,?_⟩
    change mathieuOctadExteriorPerm O (mathieuOctadCharacterLift O t) i=k
    rw [mathieuOctadCharacterLift_exterior]
    exact ht
  have hb : Function.Bijective f := (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hs,(mathieuOctadPointwise_order O).trans (octadExterior_card O).symm⟩
  obtain ⟨g,hg⟩ := hs j
  refine ⟨g,hg,?_⟩
  intro h hh
  exact hb.injective (hh.trans hg.symm)

end Atlas.Fischer
