import Atlas.Rudvalis.FrameComparison
import Atlas.Rudvalis.DistinguishedReflection
import Atlas.Rudvalis.SeedAFibreOrbit
import Atlas.Rudvalis.SecondFrameUnitAction

namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

noncomputable def frameSignCode : codeGroup := seedARowSign (binaryLabel 1)
noncomputable def frameSign : RationalSpace ≃ₗ[ℚ] RationalSpace :=
  rationalMonomialHom frameSignCode.val

theorem originalFrame_expansion (v : RationalSpace) :
    (∑i,(seedTransportLinear.symm v i/2) • originalFrame i)=v := by
  classical
  have he : (∑i,(seedTransportLinear.symm v i/2) • (Pi.single i 2 : SeedCoordinate→ℚ))=
      seedTransportLinear.symm v := by
    ext j
    simp [Pi.single_apply,ite_smul,smul_ite,Pi.smul_apply]
  calc
    _=seedTransportLinear (∑i,(seedTransportLinear.symm v i/2) • (Pi.single i 2 : SeedCoordinate→ℚ)) := by
      simp [originalFrame,map_sum,map_smul]
    _=v := by rw [he,LinearEquiv.apply_symm_apply]

theorem originalFrame_ext {f g : RationalSpace →ₗ[ℚ] RationalSpace}
    (h : ∀i,f (originalFrame i)=g (originalFrame i)) : f=g := by
  apply LinearMap.ext
  intro v
  conv_lhs => rw [←originalFrame_expansion v]
  conv_rhs => rw [←originalFrame_expansion v]
  simp only [map_sum,map_smul,h]

theorem frameSign_transport (w : SeedCoordinate→ℚ) :
    frameSign (seedTransportLinear w)=seedTransportLinear
      (fun z => if z.1=0 ∨ z.1=4 ∨ z.1=5 then w z else -w z) := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change liftedSign (dot (binaryLabel 1) (rowLabel r).val)
    (seedTransportLinear w (seedCoordinateEquiv (r,k)))=_
  rw [seedTransportLinear_apply,seedTransportLinear_apply]
  have hr : dot (binaryLabel 1) (rowLabel r).val=0 ↔ r=0 ∨r=4 ∨r=5 := by decide +kernel +revert
  simp only [liftedSign,hr]
  split_ifs <;> simp_all

theorem frameSign_originalFrame (i : SeedCoordinate) :
    frameSign (originalFrame i)=
      if i.1=0 ∨i.1=4 ∨i.1=5 then originalFrame i else -originalFrame i := by
  classical
  rw [originalFrame,frameSign_transport]
  have he : (fun z : SeedCoordinate => if z.1=0 ∨z.1=4 ∨z.1=5 then
      (Pi.single i 2 : SeedCoordinate→ℚ) z else -(Pi.single i 2 : SeedCoordinate→ℚ) z)=
      if i.1=0 ∨i.1=4 ∨i.1=5 then Pi.single i 2 else -(Pi.single i 2 : SeedCoordinate→ℚ) := by
    ext z
    by_cases hz : z=i
    · subst z; split_ifs <;> simp_all
    · split_ifs <;> simp_all [Pi.single_apply, Ne.symm hz]
  rw [he]
  split <;> simp_all [originalFrame]

theorem distinguishedReflection_frameComparison (v : RationalSpace) :
    distinguishedReflection (frameComparison v)=frameComparison (frameSign v) := by
  have he : distinguishedReflection.toLinearMap.comp frameComparison.toLinearMap=
      frameComparison.toLinearMap.comp frameSign.toLinearMap := by
    apply originalFrame_ext
    intro i
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,frameComparison_originalFrame,
      distinguishedReflection_basis,frameSign_originalFrame]
    split <;> simp [frameComparison_originalFrame]
  exact congrArg (fun f : RationalSpace→ₗ[ℚ]RationalSpace => f v) he

/-- Ambient conjugacy only; this theorem asserts no lattice preservation for S. -/
theorem distinguishedReflection_conjugacy :
    distinguishedReflection=frameComparison*frameSign*frameComparison⁻¹ := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := frameComparison.surjective v
  simpa using distinguishedReflection_frameComparison w


theorem codeUnit_originalFrame (u : Fin 8) (r : Fin 7) (k : Fin 8) :
    rationalMonomialHom (codeUnit u).val (originalFrame (r,k))=
      if seedUnitSign u (seedUnitSource u k) then -originalFrame (r,seedUnitSource u k)
      else originalFrame (r,seedUnitSource u k) := by
  change liftedCoordinateHom (seedConjugateMonomial (seedUnitMonomial u))
    (seedTransportLinear (Pi.single (r,k) 2))=_
  rw [seedConjugate_lifted_transport,seedUnit_lifted]
  have he : seedUnitOperator u (Pi.single (r,k) 2 : SeedCoordinate→ℚ)=
      if seedUnitSign u (seedUnitSource u k) then -Pi.single (r,seedUnitSource u k) 2
      else Pi.single (r,seedUnitSource u k) 2 := by
    funext z
    rcases z with ⟨s,l⟩
    rw [seedUnit_action]
    by_cases hr : s=r
    · subst s
      by_cases hl : l=seedUnitSource u k
      · subst l
        rw [seedUnit_source_involution]
        simp [signedBit]
        split <;> simp_all
      · have hk : seedUnitSource u l≠k := by
          intro h
          have := congrArg (seedUnitSource u) h
          exact hl (by simpa only [seedUnit_source_involution] using this)
        simp [Pi.single_apply,hl,hk,signedBit]
        split <;> simp_all
    · simp [Pi.single_apply,hr,signedBit]
      split <;> simp_all
  rw [he]
  split <;> simp_all [originalFrame]

theorem frameComparison_unit (u : Fin 8) (v : RationalSpace) :
    frameComparison (rationalMonomialHom (codeUnit u).val v)=
      rationalMonomialHom (codeUnit u).val (frameComparison v) := by
  have he : frameComparison.toLinearMap.comp (rationalMonomialHom (codeUnit u).val).toLinearMap=
      (rationalMonomialHom (codeUnit u).val).toLinearMap.comp frameComparison.toLinearMap := by
    apply originalFrame_ext
    rintro ⟨r,k⟩
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,codeUnit_originalFrame,
      frameComparison_originalFrame,secondFrame_unit]
    split <;> simp [frameComparison_originalFrame]
  exact congrArg (fun f : RationalSpace→ₗ[ℚ]RationalSpace => f v) he

theorem frameSign_unit (u : Fin 8) (v : RationalSpace) :
    frameSign (rationalMonomialHom (codeUnit u).val v)=
      rationalMonomialHom (codeUnit u).val (frameSign v) := by
  have he : frameSign.toLinearMap.comp (rationalMonomialHom (codeUnit u).val).toLinearMap=
      (rationalMonomialHom (codeUnit u).val).toLinearMap.comp frameSign.toLinearMap := by
    apply originalFrame_ext
    rintro ⟨r,k⟩
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,codeUnit_originalFrame,frameSign_originalFrame]
    split_ifs <;> simp_all [frameSign_originalFrame,codeUnit_originalFrame]
  exact congrArg (fun f : RationalSpace→ₗ[ℚ]RationalSpace => f v) he

end Atlas.Rudvalis
