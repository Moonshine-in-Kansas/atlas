import Atlas.LinearGroups.Orthogonal.Hyperbolic
import Atlas.LinearAlgebra.DotProductFiber
import Atlas.LinearAlgebra.QuadraticPairCount
import Atlas.LinearAlgebra.QuadraticZeroCount

/-! # Coordinate fibres and singular-vector counts for the standard quadratic forms -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F]

/-- Separate the two ordered hyperbolic coordinate blocks. -/
def coordinatesD : VectorD n F ≃ₗ[F] (Fin n → F) × (Fin n → F) where
  toFun v := (fun i => v (.inl i), fun i => v (.inr i))
  invFun v := Sum.elim v.1 v.2
  left_inv v := by funext i; cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual singular vectors, partitioned by their first hyperbolic block. -/
def singularDFiberEquiv : {v : VectorD n F // formD n F v=0} ≃
    Σ x : Fin n → F, {y : Fin n → F // Atlas.DotProduct.functional x y=0} where
  toFun v := ⟨fun i => v.val (.inl i),⟨fun i => v.val (.inr i),by
    simpa only [Atlas.DotProduct.functional_apply,formD_apply] using v.prop⟩⟩
  invFun p := ⟨Sum.elim p.1 p.2.val,by
    simpa only [formD_apply,Sum.elim_inl,Sum.elim_inr,Atlas.DotProduct.functional_apply]
      using p.2.prop⟩
  left_inv v := by apply Subtype.ext; funext i; cases i <;> rfl
  right_inv _ := rfl

/-- Singular vectors including zero, independently of all group-order assertions. -/
theorem card_singularD [Finite F] :
    Nat.card {v : VectorD n F // formD n F v=0} =
      Nat.card F ^ n + (Nat.card F ^ n-1)*Nat.card F ^ (n-1) := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_congr singularDFiberEquiv,Nat.card_sigma]
  have hc (x : Fin n → F) : Nat.card {y // Atlas.DotProduct.functional x y=0} =
      if x=0 then Nat.card F ^ n else Nat.card F ^ (n-1) := by
    split_ifs with hx
    · subst x; exact Atlas.DotProduct.card_zeroFiber
    · exact Atlas.DotProduct.card_fiber x hx 0
  simp_rw [hc]
  rw [Finset.sum_ite]
  have hz : (Finset.univ.filter fun x : Fin n → F => x=0) = {0} := by
    ext x
    simp
  simp [hz,Finset.filter_ne',Nat.card_eq_fintype_card]

abbrev BRemaining (x : Fin n → F) :=
  {p : (Fin n → F) × F // Atlas.DotProduct.functional x p.1 + p.2^2=0}

def remainingBZeroEquiv : BRemaining (0 : Fin n → F) ≃ (Fin n → F) where
  toFun p := p.val.1
  invFun y := ⟨(y,0),by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    ·
      have hz : p.val.2^2=0 := by simpa using p.prop
      exact ((pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp hz).symm
  right_inv _ := rfl

def remainingBEquiv (x : Fin n → F) : BRemaining x ≃
    Σ z : F, {y : Fin n → F // Atlas.DotProduct.functional x y = -z^2} where
  toFun p := ⟨p.val.2,⟨p.val.1,eq_neg_of_add_eq_zero_left p.prop⟩⟩
  invFun p := ⟨(p.2.val,p.1),by rw [p.2.prop]; ring⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_remainingB [Finite F] (x : Fin n → F) :
    Nat.card (BRemaining x) = Nat.card F ^ n := by
  classical
  letI := Fintype.ofFinite F
  by_cases hx : x=0
  · subst x
    rw [Nat.card_congr remainingBZeroEquiv,Nat.card_fun,Nat.card_fin]
  · have hn : 0<n := by
      by_contra hn
      have hn : n=0 := by omega
      subst n
      exact hx (Subsingleton.elim _ _)
    rw [Nat.card_congr (remainingBEquiv x),Nat.card_sigma]
    simp_rw [Atlas.DotProduct.card_fiber x hx]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
    simp only [Nat.cast_id]
    rw [mul_comm,← pow_succ]
    congr 1
    omega

def singularBFiberEquiv : {v : VectorB n F // formB n F v=0} ≃
    Σ x : Fin n → F, BRemaining x where
  toFun v := ⟨fun i => v.val.1 (.inl i),⟨(fun i => v.val.1 (.inr i),v.val.2),by
    simpa only [Atlas.DotProduct.functional_apply,formB_apply,formD_apply] using v.prop⟩⟩
  invFun p := ⟨(Sum.elim p.1 p.2.val.1,p.2.val.2),by
    simpa only [formB_apply,formD_apply,Sum.elim_inl,Sum.elim_inr,
      Atlas.DotProduct.functional_apply] using p.2.prop⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · funext i; cases i <;> rfl
    · rfl
  right_inv _ := rfl

/-- There are exactly q^(2n) singular vectors, including zero, in odd dimension. -/
theorem card_singularB [Finite F] :
    Nat.card {v : VectorB n F // formB n F v=0} = Nat.card F ^ (2*n) := by
  classical
  letI := Fintype.ofFinite F
  rw [Nat.card_congr singularBFiberEquiv,Nat.card_sigma]
  simp_rw [card_remainingB]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    Nat.card_fun,Nat.card_fin,Nat.cast_id,← pow_add,← two_mul]

abbrev NonzeroSingularB (n : ℕ) (F : Type*) [Field F] :=
  {v : {x : VectorB n F // formB n F x=0} // v.val≠0}
abbrev NonzeroSingularD (n : ℕ) (F : Type*) [Field F] :=
  {v : {x : VectorD n F // formD n F x=0} // v.val≠0}

theorem card_nonzero_singularB [Finite F] :
    Nat.card (NonzeroSingularB n F) = Nat.card F ^ (2*n)-1 := by
  rw [Atlas.Quadratic.card_nonzero_singular,card_singularB]

theorem card_nonzero_singularD [Finite F] :
    Nat.card (NonzeroSingularD n F) = (Nat.card F ^ n-1)*(Nat.card F ^ (n-1)+1) := by
  rw [Atlas.Quadratic.card_nonzero_singular,card_singularD,mul_add,mul_one]
  have h : 1 ≤ Nat.card F ^ n := one_le_pow₀ (by have := Finite.one_lt_card (α := F); omega)
  omega

theorem vectorD_finrank : Module.finrank F (VectorD n F) = 2*n := by
  simp [VectorD,Index,Module.finrank_pi,Fintype.card_sum,two_mul]

theorem vectorB_finrank : Module.finrank F (VectorB n F) = 2*n+1 := by
  simp [VectorB,Module.finrank_prod,vectorD_finrank,Module.finrank_self,two_mul]

theorem card_partnersB [Finite F] (u : VectorB n F) (hu : u≠0) (hq : formB n F u=0) :
    Nat.card {x : VectorB n F // formB n F x=0 ∧ (formB n F).polarBilin u x=1} =
      Nat.card F ^ (2*n-1) := by
  obtain ⟨f,hf,hef⟩ := exists_hyperbolic_partnerB u hu hq
  rw [Atlas.Quadratic.card_partners (formB n F) u f hq hf hef,vectorB_finrank]
  congr 1

theorem card_partnersD [Finite F] (u : VectorD n F) (hu : u≠0) (hq : formD n F u=0) :
    Nat.card {x : VectorD n F // formD n F x=0 ∧ (formD n F).polarBilin u x=1} =
      Nat.card F ^ (2*n-2) := by
  obtain ⟨f,hf,hef⟩ := exists_hyperbolic_partnerD u hu hq
  rw [Atlas.Quadratic.card_partners (formD n F) u f hq hf hef,vectorD_finrank]

end Atlas.Orthogonal


