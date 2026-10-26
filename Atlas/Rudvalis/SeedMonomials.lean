import Atlas.Rudvalis.SeedOrbitSymmetries
import Atlas.Rudvalis.MonomialUR
import Atlas.Codes.QuaternaryMonomial

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def seedBasisMonomial : SignedCoordinates SeedCoordinate where
  left := Multiplicative.ofAdd (fun z => if z.2=1 then 1 else 0)
  right := Equiv.prodCongr (Equiv.refl _) signedPositionIndexEquiv

noncomputable def geometricMonomial (g : SignedCoordinates SeedCoordinate) : SignedCoordinates Coordinate where
  left := Multiplicative.ofAdd (fun z => g.left.toAdd (seedCoordinateEquiv.symm z))
  right := seedCoordinateEquiv.symm.trans (g.right.trans seedCoordinateEquiv)

noncomputable def seedConjugateMonomial (g : SignedCoordinates SeedCoordinate) : SignedCoordinates Coordinate :=
  geometricMonomial (seedBasisMonomial*g*seedBasisMonomial⁻¹)

theorem geometricMonomial_apply (g : SignedCoordinates SeedCoordinate) (w : QuaternaryWord)
    (z : SeedCoordinate) :
    monomialHom (geometricMonomial g) w (seedCoordinateEquiv z)=
      monomialHom g (w ∘ seedCoordinateEquiv) z := by
  simp [geometricMonomial,monomialHom,monomialAction]

theorem seedBasisMonomial_apply (v : SeedCoordinate→ZMod 4) (z : SeedCoordinate) :
    monomialHom seedBasisMonomial v z=seedTransportLinear v (seedCoordinateEquiv z) := by
  rw [seedTransportLinear_apply]
  change signedScalar (if z.2=1 then 1 else 0) (v (z.1,signedPositionIndex z.2))=_
  split <;> simp_all [signedScalar]

theorem seedConjugateMonomial_transport (g : SignedCoordinates SeedCoordinate)
    (v : SeedCoordinate→ZMod 4) :
    monomialHom (seedConjugateMonomial g) (seedTransportLinear v)=
      seedTransportLinear (monomialHom g v) := by
  funext z
  obtain ⟨z,rfl⟩ := seedCoordinateEquiv.surjective z
  rw [seedConjugateMonomial,geometricMonomial_apply,←seedBasisMonomial_apply]
  have h : (seedTransportLinear v) ∘ seedCoordinateEquiv=monomialHom seedBasisMonomial v := by
    funext z; exact (seedBasisMonomial_apply v z).symm
  rw [h,map_mul,map_mul]
  simp

noncomputable def seedUnitMonomial (u : Fin 8) : SignedCoordinates SeedCoordinate where
  left := Multiplicative.ofAdd (fun z => if seedUnitSign u z.2 then 1 else 0)
  right := Equiv.prodCongr (Equiv.refl _)
    ⟨seedUnitSource u,seedUnitSource u,seedUnit_source_involution u,seedUnit_source_involution u⟩

noncomputable def seedPMonomial : SignedCoordinates SeedCoordinate where
  left := 1
  right := (Equiv.prodCongr seedRowCycle (Equiv.refl _)).symm

theorem seedUnitMonomial_apply (u : Fin 8) (v : SeedCoordinate→ZMod 4) :
    monomialHom (seedUnitMonomial u) v=seedUnitOperator u v := by
  funext z
  rw [show z=(z.1,z.2) from rfl,seedUnit_action]
  change signedScalar (if seedUnitSign u z.2 then 1 else 0) (v (z.1,seedUnitSource u z.2))=_
  cases h : seedUnitSign u z.2 <;> simp [h,signedScalar,signedBit]

theorem seedPMonomial_apply (v : SeedCoordinate→ZMod 4) :
    monomialHom seedPMonomial v=seedPOperator v := rfl

noncomputable def rudvalisUnitMonomial (u : Fin 8) : SignedCoordinates Coordinate :=
  seedConjugateMonomial (seedUnitMonomial u)
noncomputable def rudvalisPMonomial : SignedCoordinates Coordinate := seedConjugateMonomial seedPMonomial

theorem quaternarySeed_transport (t : SeedOrbitIndex) :
    quaternarySeed t=seedTransportLinear (fun z => (seedOrbitOriginal t z : ZMod 4)) := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change (signedSeedTransport (seedOrbitOriginal t) (seedCoordinateEquiv (r,k)) : ZMod 4)=_
  rw [signedSeedTransport_apply,seedTransportLinear_apply]
  simp only [signedPositionSign]
  split <;> simp_all

theorem seedUnit_cast (u : Fin 8) (v : SeedCoordinate→ℤ) :
    seedUnitOperator u (fun z => (v z : ZMod 4))=
      fun z => ((seedUnitOperator (R := ℤ) u v z : ℤ) : ZMod 4) := by
  funext z
  rw [show z=(z.1,z.2) from rfl,seedUnit_action,seedUnit_action]
  simp [signedBit]

theorem rudvalisUnitMonomial_seed (u : Fin 8) (t : SeedOrbitIndex) :
    monomialHom (rudvalisUnitMonomial u) (quaternarySeed t)=
      if seedUnitProductNegative u (seedPackedUnit t.2.1 t.2.2.1)
      then -quaternarySeed (seedUnitOrbitIndex u t)
      else quaternarySeed (seedUnitOrbitIndex u t) := by
  rw [quaternarySeed_transport, rudvalisUnitMonomial,seedConjugateMonomial_transport,
    seedUnitMonomial_apply,seedUnit_cast,seedOrbitOriginal_unit]
  split_ifs
  · simp only [Pi.neg_apply,Int.cast_neg]
    rw [show (fun z => -(seedOrbitOriginal (seedUnitOrbitIndex u t) z : ZMod 4))=
        -(fun z => (seedOrbitOriginal (seedUnitOrbitIndex u t) z : ZMod 4)) from rfl,
      map_neg,←quaternarySeed_transport]
  · exact (quaternarySeed_transport _).symm

theorem rudvalisPMonomial_seed (t : SeedOrbitIndex) :
    monomialHom rudvalisPMonomial (quaternarySeed t)=quaternarySeed (seedNextRow t.1,t.2) := by
  rw [quaternarySeed_transport,rudvalisPMonomial,seedConjugateMonomial_transport,
    seedPMonomial_apply]
  have h : seedPOperator (fun z => (seedOrbitOriginal t z : ZMod 4))=
      fun z => ((seedPOperator (R := ℤ) (seedOrbitOriginal t) z : ℤ) : ZMod 4) := rfl
  rw [h,seedOrbitOriginal_P,←quaternarySeed_transport]

end Atlas.Rudvalis
