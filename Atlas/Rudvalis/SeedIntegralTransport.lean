import Atlas.Rudvalis.LatticeMonomial

/-! Signed-coordinate transport over arbitrary coefficient rings, without reduction arguments. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
variable {ι : Type*} {R : Type*} [CommRing R]

def liftedCoordinateAction (g : SignedCoordinates ι) : (ι→R) ≃ₗ[R] (ι→R) where
  toFun v i := liftedSign (g.left.toAdd i) (v (g.right.symm i))
  invFun v i := liftedSign (g.left.toAdd (g.right i)) (v (g.right i))
  left_inv v := by ext i; simp [liftedSign]; split <;> simp_all
  right_inv v := by ext i; simp [liftedSign]; split <;> simp_all
  map_add' v w := by ext i; simp [liftedSign]; split <;> simp_all [add_comm]
  map_smul' a v := by ext i; simp [liftedSign]

def liftedCoordinateHom : SignedCoordinates ι →* ((ι→R) ≃ₗ[R] (ι→R)) where
  toFun := liftedCoordinateAction
  map_one' := by ext v i; change liftedSign 0 (v i)=v i; simp [liftedSign]
  map_mul' g h := by
    ext v i
    change liftedSign (g.left.toAdd i+h.left.toAdd (g.right.symm i))
      (v (h.right.symm (g.right.symm i)))=
      liftedSign (g.left.toAdd i) (liftedSign (h.left.toAdd (g.right.symm i))
        (v (h.right.symm (g.right.symm i))))
    exact liftedSign_add _ _ _

theorem geometricLifted_apply (g : SignedCoordinates SeedCoordinate) (w : Coordinate→R)
    (z : SeedCoordinate) :
    liftedCoordinateHom (geometricMonomial g) w (seedCoordinateEquiv z)=
      liftedCoordinateHom g (w ∘ seedCoordinateEquiv) z := by
  simp [geometricMonomial,liftedCoordinateHom,liftedCoordinateAction]

theorem seedBasisLifted_apply (v : SeedCoordinate→R) (z : SeedCoordinate) :
    liftedCoordinateHom seedBasisMonomial v z=seedTransportLinear v (seedCoordinateEquiv z) := by
  rw [seedTransportLinear_apply]
  change liftedSign (if z.2=1 then 1 else 0) (v (z.1,signedPositionIndex z.2))=_
  split <;> simp_all [liftedSign]

theorem seedConjugate_lifted_transport (g : SignedCoordinates SeedCoordinate)
    (v : SeedCoordinate→R) :
    liftedCoordinateHom (seedConjugateMonomial g) (seedTransportLinear v)=
      seedTransportLinear (liftedCoordinateHom g v) := by
  funext z
  obtain ⟨z,rfl⟩ := seedCoordinateEquiv.surjective z
  rw [seedConjugateMonomial,geometricLifted_apply,←seedBasisLifted_apply]
  have h : (seedTransportLinear v) ∘ seedCoordinateEquiv=liftedCoordinateHom seedBasisMonomial v := by
    funext z; exact (seedBasisLifted_apply v z).symm
  rw [h,map_mul,map_mul]
  simp

theorem seedUnit_lifted (u : Fin 8) (v : SeedCoordinate→R) :
    liftedCoordinateHom (seedUnitMonomial u) v=seedUnitOperator u v := by
  funext z
  rw [show z=(z.1,z.2) from rfl,seedUnit_action]
  change liftedSign (if seedUnitSign u z.2 then 1 else 0) (v (z.1,seedUnitSource u z.2))=_
  cases h : seedUnitSign u z.2 <;> simp [liftedSign,signedBit,h]

theorem seedP_lifted (v : SeedCoordinate→R) :
    liftedCoordinateHom seedPMonomial v=seedPOperator v := rfl

theorem signedSeedTransport_eq_linear (v : SeedCoordinate→ℤ) :
    signedSeedTransport v=seedTransportLinear v := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  rw [signedSeedTransport_apply,seedTransportLinear_apply]
  simp [signedPositionSign]

theorem integerMonomial_unit_transport (u : Fin 8) (v : SeedCoordinate→ℤ) :
    integerMonomial (rudvalisUnitMonomial u) (signedSeedTransport v)=
      signedSeedTransport (seedUnitOperator u v) := by
  rw [signedSeedTransport_eq_linear,signedSeedTransport_eq_linear]
  exact (seedConjugate_lifted_transport (seedUnitMonomial u) v).trans
    (congrArg seedTransportLinear (seedUnit_lifted u v))

end Atlas.Rudvalis
