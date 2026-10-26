import Atlas.LinearGroups.Chevalley.Integral.MinusculeA
import Atlas.Algebra.CyclicLatticeQuotient

/-! Exact type-A weight/root quotient, uniformly in rank. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeA
open Classical TypeAData

private theorem weightedDifferences (r : ℕ) (v : Fin (r+1) → ℤ) :
    (∑ i : Fin r, (i.val+1 : ℤ) * (v i.castSucc - v i.succ)) =
      (∑ j, v j) - (r+1 : ℤ) * v (Fin.last r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin r, (i.val+1 : ℤ) *
        (v i.castSucc.castSucc - v i.succ.castSucc)) +
      (r+1 : ℤ) * (v (Fin.last r).castSucc - v (Fin.last (r+1))) = _
    rw [ih (fun i => v i.castSucc), Fin.sum_univ_castSucc v]
    push_cast
    ring

def residue (r : ℕ) : WeightLattice (pairing (r+1)) →ₗ[ℤ] ZMod (r+1) where
  toFun μ := ((∑ i : Fin r, (i.val+1 : ℤ) *
    μ (corootElement (pairing (r+1)) (simpleRoot i))) : ℤ)
  map_add' μ ν := by simp [LinearMap.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z μ := by
    simp [LinearMap.smul_apply, Finset.mul_sum, mul_left_comm]

@[simp] theorem residue_naturalWeight (r : ℕ) (k : Fin (r+1)) :
    residue r (naturalWeight k) = 1 := by
  change ((∑ i : Fin r, (i.val+1 : ℤ) *
    naturalWeight k (corootElement (pairing (r+1)) (simpleRoot i)) : ℤ) : ZMod (r+1)) = 1
  simp only [naturalWeight_pairing, simpleRoot]
  rw [weightedDifferences r (fun j => if j = k then 1 else 0)]
  simp

theorem root_residue (r : ℕ) (a : Root (r+1)) :
    residue r (rootWeight (pairing (r+1)) a) = 0 := by
  rw [rootWeight_eq_difference, map_sub, residue_naturalWeight, residue_naturalWeight]
  exact sub_self _

theorem rootLattice_le_residue_ker (r : ℕ) :
    rootLattice (pairing (r+1)) ≤ LinearMap.ker (residue r) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact root_residue r a

theorem rootLattice_sup_selected (r : ℕ) :
    rootLattice (pairing (r+1)) ⊔
      Submodule.span ℤ {naturalWeight (0 : Fin (r+1))} = ⊤ := by
  simpa only [rootLattice, Submodule.span_union] using root_and_one_weight_span r

theorem sum_naturalWeight (r : ℕ) :
    (∑ k : Fin (r+1), naturalWeight k) = 0 := by
  apply (corootBasis (pairing (r+1)) (base r)).ext
  intro j
  obtain ⟨j,rfl⟩ := (baseIndexEquiv r).surjective j
  have hb : corootBasis (pairing (r+1)) (base r) (baseIndexEquiv r j) =
      corootElement (pairing (r+1)) (simpleRoot j) := by
    apply Subtype.ext
    exact (base r).flip.coe_toWeightBasisInt_apply
      (⟨simpleRoot j, (baseIndexEquiv r j).property⟩ : (base r).flip.support)
  rw [hb]
  simp [LinearMap.sum_apply, naturalWeight_pairing, simpleRoot, Finset.sum_sub_distrib]

theorem selected_multiple_mem (r : ℕ) :
    (r+1 : ℤ) • naturalWeight (0 : Fin (r+1)) ∈ rootLattice (pairing (r+1)) := by
  have hm (k : Fin (r+1)) : naturalWeight (0 : Fin (r+1)) - naturalWeight k ∈
      rootLattice (pairing (r+1)) := by
    by_cases hk : k=0
    · subst k
      simp
    · have h : (0 : Fin (r+1)) ≠ k := Ne.symm hk
      rw [← rootWeight_eq_difference (⟨(0,k),h⟩ : Root (r+1))]
      exact rootWeight_mem_rootLattice _ _
  have hsum : (∑ k : Fin (r+1),
      (naturalWeight (0 : Fin (r+1)) - naturalWeight k)) ∈
      rootLattice (pairing (r+1)) :=
    (rootLattice (pairing (r+1))).sum_mem (fun k _ => hm k)
  simpa only [Finset.sum_sub_distrib, sum_naturalWeight, sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℤ,
    Nat.cast_add, Nat.cast_one] using hsum

theorem rootLattice_eq_residue_ker (r : ℕ) :
    rootLattice (pairing (r+1)) = LinearMap.ker (residue r) :=
  (Atlas.Algebra.latticeCharacter_ker_eq _ (naturalWeight (0 : Fin (r+1))) (r+1)
    (residue r) (rootLattice_le_residue_ker r) (rootLattice_sup_selected r)
    (by simp) (selected_multiple_mem r)).symm

def weightRootQuotientEquiv (r : ℕ) :
    (WeightLattice (pairing (r+1)) ⧸ rootLattice (pairing (r+1))) ≃ₗ[ℤ] ZMod (r+1) :=
  Atlas.Algebra.cyclicLatticeQuotientEquiv _ (naturalWeight (0 : Fin (r+1))) (r+1)
    (residue r) (rootLattice_le_residue_ker r) (rootLattice_sup_selected r)
    (by simp) (selected_multiple_mem r)

@[simp] theorem weightRootQuotientEquiv_selected (r : ℕ) :
    weightRootQuotientEquiv r (Submodule.Quotient.mk (naturalWeight 0)) = 1 := by
  change residue r (naturalWeight 0) = 1
  simp

theorem weightRootQuotient_card (r : ℕ) :
    Nat.card (WeightLattice (pairing (r+1)) ⧸ rootLattice (pairing (r+1))) = r+1 :=
  Atlas.Algebra.cyclicLatticeQuotient_card _ (naturalWeight (0 : Fin (r+1))) (r+1)
    (residue r) (rootLattice_le_residue_ker r) (rootLattice_sup_selected r)
    (by simp) (selected_multiple_mem r)

end Atlas.Chevalley.Integral.Minuscule.TypeA
