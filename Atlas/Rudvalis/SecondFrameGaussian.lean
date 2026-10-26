import Atlas.Rudvalis.SecondFrameGlueProjection
import Atlas.Rudvalis.SeedIntegralTransport

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

private theorem integerMonomial_unit_seed (u : Fin 8) (t : SeedOrbitIndex) :
    integerMonomial (rudvalisUnitMonomial u) (seedOrbitWord t)=
      if seedUnitProductNegative u (seedPackedUnit t.2.1 t.2.2.1) then
        -seedOrbitWord (seedUnitOrbitIndex u t) else seedOrbitWord (seedUnitOrbitIndex u t) := by
  change integerMonomial (rudvalisUnitMonomial u) (signedSeedTransport (seedOrbitOriginal t))=_
  rw [integerMonomial_unit_transport,seedOrbitOriginal_unit]
  split <;> simp_all [seedOrbitWord,signedSeedTransport_eq_linear]

private theorem secondFrameI_data (r : Fin 7) (k : Fin 8) :
    seedUnitOrbitIndex 4 (secondFrameOrbitIndex (r,k))=
      secondFrameOrbitIndex (r,seedIIndex k) ∧
    (if seedUnitProductNegative 4 (seedPackedUnit
      (secondFrameOrbitIndex (r,k)).2.1 (secondFrameOrbitIndex (r,k)).2.2.1)
      then -secondFrameSign k else secondFrameSign k)=
      (if k.val%2=0 then secondFrameSign (seedIIndex k) else -secondFrameSign (seedIIndex k)) := by
  decide +kernel +revert

theorem secondFrameInteger_I (r : Fin 7) (k : Fin 8) :
    integerMonomial codeI.val (secondFrameInteger (r,k))=
      if k.val%2=0 then secondFrameInteger (r,seedIIndex k)
      else -secondFrameInteger (r,seedIIndex k) := by
  change liftedCoordinateHom codeI.val (secondFrameSign k • seedOrbitWord (secondFrameOrbitIndex (r,k)))=_
  rw [map_smul]
  change secondFrameSign k • integerMonomial (rudvalisUnitMonomial 4) (seedOrbitWord (secondFrameOrbitIndex (r,k)))=_
  rw [integerMonomial_unit_seed,(secondFrameI_data r k).1]
  have hs := (secondFrameI_data r k).2
  unfold secondFrameInteger
  split_ifs at hs ⊢ <;>
    simpa only [smul_neg,neg_smul] using congrArg
      (fun n : ℤ => n • seedOrbitWord (secondFrameOrbitIndex (r,seedIIndex k))) hs

theorem secondFrame_I (r : Fin 7) (k : Fin 8) :
    rationalI (secondFrame (r,k))=
      if k.val%2=0 then secondFrame (r,seedIIndex k) else -secondFrame (r,seedIIndex k) := by
  change rationalMonomialHom codeI.val (halfCoordinates (secondFrameInteger (r,k)))=_
  rw [rationalMonomial_half,secondFrameInteger_I]
  split <;> simp_all [secondFrame]

theorem frameGlueMask_mem_iff_row (z : SeedCoordinate) :
    z∈frameGlueMask ↔ ∃i : Fin 3,frameGluePoint i=rowLabel z.1 := by
  classical
  constructor
  · intro hz
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hz
    have he := congrArg originalCoordinateEquiv ha
    change originalCoordinateEquiv (originalCoordinateEquiv.symm (frameGluePoint a.1,a.2))=originalCoordinateEquiv z at he
    rw [Equiv.apply_symm_apply] at he
    exact ⟨a.1,congrArg Prod.fst he⟩
  · rintro ⟨i,hi⟩
    apply Finset.mem_image.mpr
    refine ⟨(i,(originalCoordinateEquiv z).2),Finset.mem_univ _,?_⟩
    apply originalCoordinateEquiv.injective
    change originalCoordinateEquiv (originalCoordinateEquiv.symm (frameGluePoint i,(originalCoordinateEquiv z).2))=originalCoordinateEquiv z
    rw [Equiv.apply_symm_apply]
    exact Prod.ext hi rfl

theorem frameGlueMask_I (r : Fin 7) (k : Fin 8) :
    (r,seedIIndex k)∈frameGlueMask ↔ (r,k)∈frameGlueMask := by
  rw [frameGlueMask_mem_iff_row,frameGlueMask_mem_iff_row]

theorem frameGlueProjection_gaussian (v : RationalSpace) :
    frameGlueProjection (rationalI v)=rationalI (frameGlueProjection v) := by
  have hp (z : SeedCoordinate) : frameGlueProjection (secondFrame z)=
      if z∈frameGlueMask then secondFrame z else 0 := by
    change secondFrameProjection frameGlueMask (secondFrame z)=_
    rw [←secondFrameBasis_apply,secondFrameProjection_basis,secondFrameBasis_apply]
  have he : frameGlueProjection.comp rationalI.toLinearMap=
      rationalI.toLinearMap.comp frameGlueProjection := by
    apply secondFrameBasis.ext
    rintro ⟨r,k⟩
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,secondFrameBasis_apply]
    by_cases hm : (r,k)∈frameGlueMask
    · have hn := (frameGlueMask_I r k).mpr hm
      by_cases hk : k.val%2=0 <;> simp [secondFrame_I,hp,hm,hn,hk]
    · have hn : (r,seedIIndex k)∉frameGlueMask := fun h => hm ((frameGlueMask_I r k).mp h)
      by_cases hk : k.val%2=0 <;> simp [secondFrame_I,hp,hm,hn,hk]
  exact congrArg (fun f : RationalSpace→ₗ[ℚ]RationalSpace => f v) he

theorem frameGlueReflection_gaussian (v : RationalSpace) :
    frameGlueReflection (rationalI v)=rationalI (frameGlueReflection v) := by
  change (2 : ℚ) • frameGlueProjection (rationalI v)-rationalI v=
    rationalI ((2 : ℚ) • frameGlueProjection v-v)
  rw [map_sub,map_smul,frameGlueProjection_gaussian]

end Atlas.Rudvalis
