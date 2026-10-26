import Atlas.Rudvalis.FramePowerCertificate
namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def frameStep : RationalSpace ≃ₗ[ℚ] RationalSpace := frameSign*frameComparison

 theorem frameSign_raw_formula (v : RationalSpace) (j : SeedCoordinate) :
    seedTransportLinear.symm (frameSign v) j=
      if j.1=0 ∨j.1=4 ∨j.1=5 then seedTransportLinear.symm v j else -seedTransportLinear.symm v j := by
  obtain ⟨w,rfl⟩ := seedTransportLinear.surjective v
  rw [frameSign_transport]
  simp

theorem frameStep_raw_formula (v : RationalSpace) (j : SeedCoordinate) :
    seedTransportLinear.symm (frameStep v) j=
      ∑i,seedTransportLinear.symm v i*(frameStepNumerator j i:ℚ)/4 := by
  change seedTransportLinear.symm (frameSign (frameComparison v)) j=_
  rw [frameSign_raw_formula,frameComparison_raw_formula]
  unfold frameStepNumerator
  split_ifs with h
  · simp
  · simp only [Int.cast_mul,Int.cast_neg,Int.cast_one,neg_one_mul]
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

noncomputable def framePowerVector (n : Fin 8) (r : Fin 7) : RationalSpace :=
  seedTransportLinear (fun j => (framePowerNumerator n r j:ℚ)/(4:ℚ)^n.val)

theorem framePowerVector_step (n : Fin 7) (r : Fin 7) :
    frameStep (framePowerVector n.castSucc r)=framePowerVector n.succ r := by
  apply seedTransportLinear.symm.injective
  funext j
  rw [frameStep_raw_formula]
  simp only [framePowerVector,LinearEquiv.symm_apply_apply,Fin.val_castSucc,Fin.val_succ]
  rw [framePowerNumerator_step]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

theorem framePowerVector_pow (n : Fin 8) (r : Fin 7) :
    (frameStep^n.val) (framePowerVector 0 r)=framePowerVector n r := by
  induction n using Fin.induction with
  | zero => simp
  | succ n ih =>
    simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ,pow_succ',LinearEquiv.mul_apply,ih]
    exact framePowerVector_step n r

theorem framePowerVector_seven (r : Fin 7) :
    framePowerVector 7 r=-framePowerVector 0 r := by
  unfold framePowerVector
  rw [←map_neg]
  congr 1
  funext j
  simp only [Pi.neg_apply]
  rw [framePowerNumerator_seven,framePowerNumerator_zero]
  split_ifs <;> norm_num

theorem frameStep_seventh_base (r : Fin 7) :
    (frameStep^7) (originalFrame (r,1))=-originalFrame (r,1) := by
  have he : originalFrame (r,1)=(2:ℚ) • framePowerVector 0 r := by
    rw [originalFrame,framePowerVector,←map_smul]
    congr 1
    ext j
    simp [framePowerNumerator_zero,Pi.single_apply]
  have hp := framePowerVector_pow (7:Fin 8) r
  change (frameStep^7) (framePowerVector 0 r)=framePowerVector 7 r at hp
  rw [he,map_smul,hp,framePowerVector_seven,smul_neg]

theorem frameStep_unit (u : Fin 8) (v : RationalSpace) :
    frameStep (rationalMonomialHom (codeUnit u).val v)=
      rationalMonomialHom (codeUnit u).val (frameStep v) := by
  exact (congrArg frameSign (frameComparison_unit u v)).trans (frameSign_unit u _)

theorem frameStep_pow_unit (n : ℕ) (u : Fin 8) (v : RationalSpace) :
    (frameStep^n) (rationalMonomialHom (codeUnit u).val v)=
      rationalMonomialHom (codeUnit u).val ((frameStep^n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',LinearEquiv.mul_apply,LinearEquiv.mul_apply,ih,frameStep_unit]

theorem frameStep_seventh_original (i : SeedCoordinate) :
    (frameStep^7) (originalFrame i)=-originalFrame i := by
  rcases i with ⟨r,k⟩
  obtain ⟨u,hu⟩ : ∃u:Fin 8,seedUnitSource u 1=k := by decide +kernel +revert
  have he := frameStep_pow_unit 7 u (originalFrame (r,1))
  rw [frameStep_seventh_base,codeUnit_originalFrame,map_neg,codeUnit_originalFrame,hu] at he
  split_ifs at he
  · simpa using congrArg Neg.neg he
  · exact he

theorem frameStep_seventh (v : RationalSpace) : (frameStep^7) v=-v := by
  have he : (frameStep^7).toLinearMap= -LinearMap.id := by
    apply originalFrame_ext
    exact frameStep_seventh_original
  exact congrArg (fun f:RationalSpace→ₗ[ℚ]RationalSpace=>f v) he

theorem frameSign_involutive : Function.Involutive frameSign := by
  intro v
  obtain ⟨w,rfl⟩ := seedTransportLinear.surjective v
  rw [frameSign_transport,frameSign_transport]
  congr 1
  funext j
  split_ifs <;> simp

theorem frameSign_distinguishedReflection :
    frameSign*distinguishedReflection=frameStep^2 := by
  apply LinearEquiv.ext
  intro v
  have he := distinguishedReflection_frameComparison (frameComparison v)
  rw [frameComparison_involutive] at he
  change frameSign (distinguishedReflection v)=_
  rw [he,pow_two]
  rfl

/-- The frame exchange is a word in the row sign and the distinguished reflection.
This ambient identity itself makes no assertion of lattice preservation. -/
theorem frameComparison_exchange_identity (v : RationalSpace) :
    frameComparison v= -frameSign (((frameSign*distinguishedReflection)^4) v) := by
  rw [frameSign_distinguishedReflection,←pow_mul]
  change frameComparison v= -frameSign ((frameStep^8) v)
  rw [show (8:ℕ)=1+7 from rfl,pow_add,pow_one,LinearEquiv.mul_apply,
    frameStep_seventh,map_neg]
  change frameComparison v= -frameSign (-(frameSign (frameComparison v)))
  rw [map_neg,neg_neg,frameSign_involutive]
end Atlas.Rudvalis
