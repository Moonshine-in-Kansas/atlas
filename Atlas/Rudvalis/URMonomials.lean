import Atlas.Rudvalis.SeedCodeSymmetries
import Atlas.Rudvalis.URPreservation

/-! The displayed U and R as elements of the full signed code stabilizer. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def seedUMonomial : SignedCoordinates SeedCoordinate where
  left := Multiplicative.ofAdd (fun z => if seedUSign z.1 z.2 then 1 else 0)
  right := seedUCoord.symm
noncomputable def seedRMonomial : SignedCoordinates SeedCoordinate where
  left := Multiplicative.ofAdd (fun z => if seedRSign z.1 z.2 then 1 else 0)
  right := seedRCoord.symm

noncomputable def rudvalisUMonomial := seedConjugateMonomial seedUMonomial
noncomputable def rudvalisRMonomial := seedConjugateMonomial seedRMonomial

theorem seedUMonomial_apply (v : SeedCoordinate→ZMod 4) :
    monomialHom seedUMonomial v=seedUOperator v := by
  funext z
  change signedScalar (if seedUSign z.1 z.2 then 1 else 0) (v (seedUCoord z))=_
  cases h : seedUSign z.1 z.2 <;> simp [signedScalar,seedUOperator,signedCoordinateOperator,h]

theorem seedRMonomial_apply (v : SeedCoordinate→ZMod 4) :
    monomialHom seedRMonomial v=seedROperator v := by
  funext z
  change signedScalar (if seedRSign z.1 z.2 then 1 else 0) (v (seedRCoord z))=_
  cases h : seedRSign z.1 z.2 <;> simp [signedScalar,seedROperator,signedCoordinateOperator,h]

theorem rudvalisUMonomial_apply (w : QuaternaryWord) :
    monomialHom rudvalisUMonomial w=rudvalisUOperator w := by
  obtain ⟨v,rfl⟩ := seedTransportLinear.surjective w
  rw [rudvalisUMonomial,seedConjugateMonomial_transport,seedUMonomial_apply]
  simp [rudvalisUOperator]

theorem rudvalisRMonomial_apply (w : QuaternaryWord) :
    monomialHom rudvalisRMonomial w=rudvalisROperator w := by
  obtain ⟨v,rfl⟩ := seedTransportLinear.surjective w
  rw [rudvalisRMonomial,seedConjugateMonomial_transport,seedRMonomial_apply]
  simp [rudvalisROperator]

noncomputable def codeU : codeGroup := ⟨rudvalisUMonomial,by
  apply codeGroup_mem_of_preserves
  intro w hw
  rw [rudvalisUMonomial_apply]
  exact rudvalisU_preserves w hw⟩

noncomputable def codeR : codeGroup := ⟨rudvalisRMonomial,by
  apply codeGroup_mem_of_preserves
  intro w hw
  rw [rudvalisRMonomial_apply]
  exact rudvalisR_preserves w hw⟩

end Atlas.Rudvalis
