import Atlas.Tits.FiveQuartetAction
import Atlas.GroupTheory.FivePointImageOrder

namespace Atlas.Tits
open Atlas.Rudvalis
open Atlas.Codes.Quaternary
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

noncomputable def pairBeta : pairStabilizer :=
  codePairHom ⟨coupleCodeBeta,coupleCodeBeta_mem⟩

noncomputable def fiveQuartetBeta : Equiv.Perm FiveQuartets := fiveQuartetHom pairBeta

theorem fiveQuartetHom_pow_apply (g : pairStabilizer) (n : ℕ) (Q : FiveQuartets) :
    (fiveQuartetHom g ^ n) Q = g ^ n • Q := by
  rw [←map_pow]
  rfl

theorem codePair_power_cross (k : codeCoupleStabilizer) (n : ℕ) (c : MinimalCross) :
    ((codePairHom k)^n).val.val • c=(k.val^n) • c := by
  rw [←map_pow]
  change codeGaussianHom (k^n).val • c=(k.val^n) • c
  rw [codeGaussianHom_cross]
  rfl


theorem coupleBeta_power_coordinates (n : ℕ) (z : SeedCoordinate) :
    (coupleCodeBeta^n).val.right (originalCoordinateEquiv z)=
      originalCoordinateEquiv ((coupleOriginalBeta.right^n) z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Subgroup.coe_mul]
    change coupleCodeBeta.val.right ((coupleCodeBeta^n).val.right (originalCoordinateEquiv z))=_
    rw [ih,coupleCodeBeta_transport]
    change (seedConjugateMonomial coupleOriginalBeta).right
      (originalCoordinateEquiv ((coupleOriginalBeta.right^n) z))=_
    rw [seedConjugateMonomial_right,original_congr_apply]
    rw [pow_succ' coupleOriginalBeta.right]
    rfl

theorem pairBeta_mem_monomial : pairBeta∈monomialPairGroup :=
  ⟨⟨coupleCodeBeta,coupleCodeBeta_mem⟩,rfl⟩

/-- The element comes from the actual order-4096 monomial pair group. Its
five-point permutation therefore has 2-power order dividing the exponent60. -/
theorem fiveQuartetBeta_fourth : fiveQuartetBeta^4=1 := by
  have h2 : orderOf fiveQuartetBeta ∣ 4096 := by
    have h := monomialPairGroup.orderOf_dvd_natCard pairBeta_mem_monomial
    rw [cardMonomialPairGroup] at h
    exact (orderOf_map_dvd fiveQuartetHom pairBeta).trans h
  have h60 : orderOf fiveQuartetBeta ∣ 60 := orderOf_dvd_of_pow_eq_one
    (Atlas.GroupTheory.perm_five_pow_sixty cardFiveQuartets fiveQuartetBeta)
  have h4 := Nat.dvd_gcd h2 h60
  norm_num at h4
  exact orderOf_dvd_iff_pow_eq_one.mp h4

noncomputable def betaPlaneQuartet : FiveQuartets :=
  ⟨coordinatePlaneQuartet (rowLabel 0) (rowLabel 4) referencePlaneNormal 0 0,
    coordinatePlaneQuartet_isQuartet _ _ _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) 0 0,by
      rintro c (rfl|rfl)
      · rw [localReferenceCross_eq]
        exact Or.inl ⟨0,by decide +kernel,rfl⟩
      · rw [referenceSecondCross_eq]
        exact Or.inl ⟨binaryLabel 2,by decide +kernel,rfl⟩⟩

theorem betaPlane_initial_coordinate :
    coordinateCross (originalCoordinateEquiv (4,0))∈betaPlaneQuartet.val := by
  apply Or.inr
  exact ⟨(originalCoordinateEquiv (4,0)).2,by decide +kernel,rfl⟩


theorem betaPlane_squared_coordinate_not_mem :
    coordinateCross (originalCoordinateEquiv ((coupleOriginalBeta.right^2) (4,0)))∉
      betaPlaneQuartet.val := by
  let i := originalCoordinateEquiv ((coupleOriginalBeta.right^2) (4,0))
  have hr : i.1=rowLabel 4 := by decide +kernel
  have hd : dot referencePlaneNormal.val i.2=1 := by decide +kernel
  have he : i=(rowLabel 4,i.2) := Prod.ext hr rfl
  change coordinateCross i∉coordinatePlaneQuartet (rowLabel 0) (rowLabel 4) referencePlaneNormal 0 0
  rw [he]
  rintro (h|h)
  · have hh := coordinatePlaneSlice_subset _ _ _ h
    have hn := (coordinateCross_mem_row_iff _ _ _).mp hh
    exact (by decide +kernel : rowLabel 4≠rowLabel 0) hn.symm
  · have hh := (coordinatePlaneSlice_mem _ _ (by decide +kernel) 0 i.2).mp h
    rw [hd] at hh
    exact one_ne_zero hh


theorem fiveQuartetBeta_square_ne_one : fiveQuartetBeta^2≠1 := by
  intro h
  have he := congrArg (fun e : Equiv.Perm FiveQuartets=>e betaPlaneQuartet) h
  have hm : coordinateCross ((coupleCodeBeta^2).val.right (originalCoordinateEquiv (4,0)))∈
      (pairBeta^2 • betaPlaneQuartet).val := by
    refine ⟨coordinateCross (originalCoordinateEquiv (4,0)),betaPlane_initial_coordinate,?_⟩
    dsimp only
    rw [pairBeta,codePair_power_cross,coordinateCross_action]
  rw [fiveQuartetBeta,fiveQuartetHom_pow_apply] at he
  change pairBeta^2 • betaPlaneQuartet=betaPlaneQuartet at he
  rw [he,coupleBeta_power_coordinates] at hm
  exact betaPlane_squared_coordinate_not_mem hm

/-- The inherited literal beta has order four in the actual five-quartet image. -/
theorem fiveQuartetBeta_order : orderOf fiveQuartetBeta=4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) fiveQuartetBeta_square_ne_one fiveQuartetBeta_fourth

theorem fiveQuartetBeta_fixes_reference : fiveQuartetBeta referenceQuartet=referenceQuartet := by
  change pairBeta∈MulAction.stabilizer pairStabilizer referenceQuartet
  rw [referenceQuartet_stabilizer_eq_monomial]
  exact ⟨⟨coupleCodeBeta,coupleCodeBeta_mem⟩,rfl⟩

end Atlas.Tits
