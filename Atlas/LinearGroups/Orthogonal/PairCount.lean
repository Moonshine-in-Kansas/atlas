import Atlas.LinearGroups.Orthogonal.SingularCount

/-! # Ordered quadratic hyperbolic pairs, counted independently of isometry-group orders -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F]

abbrev HyperbolicPairsB (n : ℕ) (F : Type*) [Field F] :=
  {p : VectorB n F × VectorB n F // formB n F p.1=0 ∧ formB n F p.2=0 ∧
    (formB n F).polarBilin p.1 p.2=1}
abbrev HyperbolicPairsD (n : ℕ) (F : Type*) [Field F] :=
  {p : VectorD n F × VectorD n F // formD n F p.1=0 ∧ formD n F p.2=0 ∧
    (formD n F).polarBilin p.1 p.2=1}

def hyperbolicPairsBFiberEquiv : HyperbolicPairsB n F ≃
    Σ u : NonzeroSingularB n F,
      {v : VectorB n F // formB n F v=0 ∧ (formB n F).polarBilin u.val.val v=1} where
  toFun p := ⟨⟨⟨p.val.1,p.prop.1⟩,by
    intro h
    change p.val.1 = 0 at h
    have hp := p.prop.2.2
    simpa only [h,map_zero,LinearMap.zero_apply,zero_ne_one] using hp⟩,
    ⟨p.val.2,p.prop.2⟩⟩
  invFun p := ⟨(p.1.val.val,p.2.val),p.1.val.prop,p.2.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

def hyperbolicPairsDFiberEquiv : HyperbolicPairsD n F ≃
    Σ u : NonzeroSingularD n F,
      {v : VectorD n F // formD n F v=0 ∧ (formD n F).polarBilin u.val.val v=1} where
  toFun p := ⟨⟨⟨p.val.1,p.prop.1⟩,by
    intro h
    change p.val.1 = 0 at h
    have hp := p.prop.2.2
    simpa only [h,map_zero,LinearMap.zero_apply,zero_ne_one] using hp⟩,
    ⟨p.val.2,p.prop.2⟩⟩
  invFun p := ⟨(p.1.val.val,p.2.val),p.1.val.prop,p.2.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_hyperbolicPairsB [Finite F] :
    Nat.card (HyperbolicPairsB n F) =
      (Nat.card F^(2*n)-1)*Nat.card F^(2*n-1) := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_congr hyperbolicPairsBFiberEquiv,Nat.card_sigma]
  have h (u : NonzeroSingularB n F) := card_partnersB u.val.val u.prop u.val.prop
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    card_nonzero_singularB,Nat.cast_id]

theorem card_hyperbolicPairsD [Finite F] :
    Nat.card (HyperbolicPairsD n F) =
      (Nat.card F^n-1)*(Nat.card F^(n-1)+1)*Nat.card F^(2*n-2) := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_congr hyperbolicPairsDFiberEquiv,Nat.card_sigma]
  have h (u : NonzeroSingularD n F) := card_partnersD u.val.val u.prop u.val.prop
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    card_nonzero_singularD,Nat.cast_id]

end Atlas.Orthogonal
