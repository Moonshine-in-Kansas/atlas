import Atlas.LinearGroups.Orthogonal.Minus.Geometry
import Atlas.LinearGroups.Orthogonal.PairOrbit

/-! Hyperbolic pairs in the actual minus space, counted before group orders. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def hyperbolicPairsFiberEquiv (hdeg : Module.finrank F K = 2) (k : ℕ) : hyperbolicPairs (form hdeg k) ≃
    Σ u : NonzeroSingular hdeg k,
      {v : Vector k F K // form hdeg k v=0 ∧ (form hdeg k).polarBilin u.val.val v=1} where
  toFun p := ⟨⟨⟨p.val.1,p.prop.1⟩,by
    intro h
    change p.val.1 = 0 at h
    have hp := p.prop.2.2
    simpa only [h,map_zero,LinearMap.zero_apply,zero_ne_one] using hp⟩,
    ⟨p.val.2,p.prop.2⟩⟩
  invFun p := ⟨(p.1.val.val,p.2.val),p.1.val.prop,p.2.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_hyperbolicPairs (hdeg : Module.finrank F K = 2) (k : ℕ) :
    Nat.card (hyperbolicPairs (form hdeg k)) =
      (Nat.card F^(k+1)+1)*(Nat.card F^k-1)*Nat.card F^(2*k) := by
  classical
  letI := Fintype.ofFinite F
  letI := Fintype.ofFinite K
  rw [Nat.card_congr (hyperbolicPairsFiberEquiv hdeg k),Nat.card_sigma]
  have h (u : NonzeroSingular hdeg k) := card_partners hdeg k u.val.val u.prop u.val.prop
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    card_nonzero_singular,Nat.cast_id]

end Atlas.Orthogonal.Minus
