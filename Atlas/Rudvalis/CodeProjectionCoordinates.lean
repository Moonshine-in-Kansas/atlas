import Atlas.Rudvalis.URMonomials

/-! Coordinate formulas for the actual signed code generators. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def originalCoordinateEquiv : SeedCoordinate ≃ Coordinate :=
  seedBasisMonomial.right.trans seedCoordinateEquiv

theorem originalCoordinateEquiv_apply (z : SeedCoordinate) :
    originalCoordinateEquiv z=(rowLabel z.1,seedInnerLabel z.1 (signedPositionIndex z.2)) := rfl

theorem seedConjugateMonomial_right (g : SignedCoordinates SeedCoordinate) :
    (seedConjugateMonomial g).right=Equiv.permCongrHom originalCoordinateEquiv g.right := by
  apply Equiv.ext
  intro z
  rfl

theorem codeP_right : codeP.val.right=Equiv.permCongrHom originalCoordinateEquiv seedPMonomial.right :=
  seedConjugateMonomial_right _

theorem codeU_right : codeU.val.right=Equiv.permCongrHom originalCoordinateEquiv seedUMonomial.right :=
  seedConjugateMonomial_right _

theorem codeR_right : codeR.val.right=Equiv.permCongrHom originalCoordinateEquiv seedRMonomial.right :=
  seedConjugateMonomial_right _

noncomputable def nineCodeGenerator (i : Fin 9) : codeGroup :=
  if h : i.val<3 then ![codeI,codeRho,codeSigma] ⟨i.val,h⟩
  else codeP^(i.val-3)*codeU*(codeP^(i.val-3))⁻¹

noncomputable def nineOriginalPermutation (i : Fin 9) : Equiv.Perm SeedCoordinate :=
  if h : i.val<3 then (seedUnitMonomial (![4,1,2] ⟨i.val,h⟩)).right
  else seedPMonomial.right^(i.val-3)*seedUMonomial.right*(seedPMonomial.right^(i.val-3))⁻¹

theorem nineCodeGenerator_right (i : Fin 9) :
    (nineCodeGenerator i).val.right=Equiv.permCongrHom originalCoordinateEquiv (nineOriginalPermutation i) := by
  unfold nineCodeGenerator nineOriginalPermutation
  split
  · rename_i h
    interval_cases i.val <;> simp_all [codeI,codeRho,codeSigma,rudvalisUnitMonomial,
      seedConjugateMonomial_right]
  · simp only [Subgroup.coe_mul,Subgroup.coe_inv,Subgroup.coe_pow]
    change SemidirectProduct.rightHom (codeP.val^(i.val-3)*codeU.val*(codeP.val^(i.val-3))⁻¹)=_
    simp only [map_mul,map_inv,map_pow]
    change codeP.val.right^(i.val-3)*codeU.val.right*(codeP.val.right^(i.val-3))⁻¹=_
    simp only [codeP_right,codeU_right,map_mul,map_inv,map_pow]

end Atlas.Rudvalis
