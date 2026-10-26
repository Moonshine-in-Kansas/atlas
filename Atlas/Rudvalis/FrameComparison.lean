import Atlas.Rudvalis.SecondFrameProjection
import Atlas.Rudvalis.SeedIntegralTransport

/-! Ambient labeled frame comparison only; no lattice preservation is assumed here. -/
namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def originalFrame (i : SeedCoordinate) : RationalSpace :=
  seedTransportLinear (Pi.single i 2)

noncomputable def halfFunctionEquiv : (SeedCoordinate→ℚ) ≃ₗ[ℚ] (SeedCoordinate→ℚ) where
  toFun v i := v i/2
  invFun v i := 2*v i
  left_inv v := by ext i; dsimp; ring
  right_inv v := by ext i; dsimp; ring
  map_add' v w := by ext i; dsimp; ring
  map_smul' a v := by ext i; dsimp; ring

noncomputable def frameComparison : RationalSpace ≃ₗ[ℚ] RationalSpace :=
  seedTransportLinear.symm.trans (halfFunctionEquiv.trans secondFrameBasis.equivFun.symm)

theorem frameComparison_formula (v : RationalSpace) :
    frameComparison v=∑i,(seedTransportLinear.symm v i/2) • secondFrame i := by
  change secondFrameBasis.equivFun.symm (halfFunctionEquiv (seedTransportLinear.symm v))=_
  rw [Module.Basis.equivFun_symm_apply]
  simp only [secondFrameBasis_apply]
  rfl

theorem frameComparison_originalFrame (i : SeedCoordinate) :
    frameComparison (originalFrame i)=secondFrame i := by
  classical
  rw [frameComparison_formula]
  simp [originalFrame,Pi.single_apply,ite_div,ite_smul]

theorem frameComparison_repr (v : RationalSpace) (i : SeedCoordinate) :
    secondFrameBasis.repr (frameComparison v) i=seedTransportLinear.symm v i/2 := by
  change secondFrameBasis.equivFun (frameComparison v) i=_
  change secondFrameBasis.equivFun (secondFrameBasis.equivFun.symm
    (halfFunctionEquiv (seedTransportLinear.symm v))) i=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem frameComparison_pairing (v w : RationalSpace) :
    rationalDot (frameComparison v) (frameComparison w)=rationalDot v w := by
  rw [secondFrame_dot_repr]
  simp_rw [frameComparison_repr]
  calc
    _=∑i,seedTransportLinear.symm v i*seedTransportLinear.symm w i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=rationalDot v w := seedTransportLinear_symm_pairing v w

noncomputable def frameComparisonRaw (i : SeedCoordinate) : SeedCoordinate→ℤ :=
  secondFrameSign i.2 • seedOrbitOriginal (secondFrameOrbitIndex i)

theorem secondFrameInteger_comparisonRaw (i : SeedCoordinate) :
    secondFrameInteger i=seedTransportLinear (frameComparisonRaw i) := by
  rw [secondFrameInteger,seedOrbitWord,signedSeedTransport_eq_linear]
  exact (seedTransportLinear.map_smul (secondFrameSign i.2) _).symm

theorem secondFrame_raw (i : SeedCoordinate) :
    secondFrame i=seedTransportLinear (fun j => (frameComparisonRaw i j : ℚ)/2) := by
  rw [secondFrame,secondFrameInteger_comparisonRaw]
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change ((seedTransportLinear (R:=ℤ) (frameComparisonRaw i) (seedCoordinateEquiv (r,k)) : ℤ) : ℚ)/2=_
  rw [seedTransportLinear_apply,seedTransportLinear_apply]
  split <;> simp_all [neg_div]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem frameComparisonRaw_symmetric (i j : SeedCoordinate) : frameComparisonRaw i j=frameComparisonRaw j i := by
  decide +kernel +revert

theorem frameComparison_raw_formula (v : RationalSpace) (j : SeedCoordinate) :
    seedTransportLinear.symm (frameComparison v) j=
      ∑i,seedTransportLinear.symm v i*(frameComparisonRaw i j : ℚ)/4 := by
  rw [frameComparison_formula]
  simp only [map_sum,map_smul,secondFrame_raw,LinearEquiv.symm_apply_apply,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem frameComparison_selfadjoint (v w : RationalSpace) :
    rationalDot (frameComparison v) w=rationalDot v (frameComparison w) := by
  unfold rationalDot
  rw [←seedTransportLinear_symm_pairing (frameComparison v) w,
    ←seedTransportLinear_symm_pairing v (frameComparison w)]
  simp_rw [frameComparison_raw_formula]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [frameComparisonRaw_symmetric j i]
  ring

theorem frameComparison_involutive : Function.Involutive frameComparison := by
  intro v
  have he (w : RationalSpace) : rationalDot (frameComparison (frameComparison v)) w=rationalDot v w := by
    rw [frameComparison_selfadjoint,frameComparison_pairing]
  funext i
  have h := he (coordinateMinimum i)
  simpa [rationalDot,coordinateMinimum,Pi.single_apply] using h

end Atlas.Rudvalis
