import Atlas.LinearGroups.Chevalley.Integral.MinusculeC
import Atlas.Algebra.CyclicLatticeQuotient

/-! The actual type-C weight/root quotient, with an explicit character. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeC
open Classical ClassicalData

def parity (n : ℕ) : WeightLattice (pairingC (n+1)) →ₗ[ℤ] ZMod 2 where
  toFun μ := (∑ i : Fin (n+1), μ (corootElement (pairingC (n+1))
    (shortRoot i 1 (Or.inl rfl))) : ℤ)
  map_add' μ ν := by simp [LinearMap.add_apply, Finset.sum_add_distrib]
  map_smul' z μ := by simp [LinearMap.smul_apply, Finset.mul_sum]

@[simp] theorem parity_naturalWeight (n : ℕ) (i : Fin (n+1)) (s : ℤ) :
    parity n (naturalWeight i s) = (s : ZMod 2) := by
  change ((∑ x : Fin (n+1), s * (Pi.single x (1 : ℤ) : Fin (n+1) → ℤ) i : ℤ) : ZMod 2) = (s : ZMod 2)
  simp [Pi.single_apply]

theorem root_parity (n : ℕ) (a : BRoot (n+1)) :
    parity n (rootWeight (pairingC (n+1)) a) = 0 := by
  rcases signed_support_classification a with ⟨_,i,s,hs,ha⟩ | ⟨i,j,hij,s,t,hs,ht,ha⟩
  · have he : a = shortRoot i s hs := Subtype.ext ha
    subst a
    rw [short_label_rootWeight, parity_naturalWeight]
    simp [show (2 : ZMod 2) = 0 from by decide]
  · have he : a = longRoot true i j hij s t hs ht := Subtype.ext ha
    subst a
    rw [long_label_rootWeight, map_add, parity_naturalWeight, parity_naturalWeight]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      norm_num <;> decide

theorem rootLattice_le_parity_ker (n : ℕ) :
    rootLattice (pairingC (n+1)) ≤ LinearMap.ker (parity n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact root_parity n a

theorem rootLattice_sup_selected (n : ℕ) :
    rootLattice (pairingC (n+1)) ⊔
      Submodule.span ℤ {naturalWeight (0 : Fin (n+1)) 1} = ⊤ := by
  simpa only [rootLattice, Submodule.span_union] using root_and_one_weight_span n

theorem selected_double_mem (n : ℕ) :
    (2 : ℤ) • naturalWeight (0 : Fin (n+1)) 1 ∈ rootLattice (pairingC (n+1)) := by
  have h : (2 : ℤ) • naturalWeight (0 : Fin (n+1)) 1 =
      rootWeight (pairingC (n+1)) (shortRoot 0 1 (Or.inl rfl)) := by
    rw [short_label_rootWeight]
    ext x
    simp [naturalWeight]
  rw [h]
  exact rootWeight_mem_rootLattice _ _

theorem rootLattice_eq_parity_ker (n : ℕ) :
    rootLattice (pairingC (n+1)) = LinearMap.ker (parity n) :=
  (Atlas.Algebra.latticeCharacter_ker_eq _ (naturalWeight (0 : Fin (n+1)) 1) 2
    (parity n) (rootLattice_le_parity_ker n) (rootLattice_sup_selected n)
    (by simp) (selected_double_mem n)).symm

def weightRootQuotientEquiv (n : ℕ) :
    (WeightLattice (pairingC (n+1)) ⧸ rootLattice (pairingC (n+1))) ≃ₗ[ℤ] ZMod 2 :=
  Atlas.Algebra.cyclicLatticeQuotientEquiv _ (naturalWeight (0 : Fin (n+1)) 1) 2
    (parity n) (rootLattice_le_parity_ker n) (rootLattice_sup_selected n)
    (by simp) (selected_double_mem n)

@[simp] theorem weightRootQuotientEquiv_selected (n : ℕ) :
    weightRootQuotientEquiv n (Submodule.Quotient.mk (naturalWeight 0 1)) = 1 := by
  change parity n (naturalWeight 0 1) = 1
  simp

theorem weightRootQuotient_card (n : ℕ) :
    Nat.card (WeightLattice (pairingC (n+1)) ⧸ rootLattice (pairingC (n+1))) = 2 :=
  Atlas.Algebra.cyclicLatticeQuotient_card _ (naturalWeight (0 : Fin (n+1)) 1) 2
    (parity n) (rootLattice_le_parity_ker n) (rootLattice_sup_selected n)
    (by simp) (selected_double_mem n)

end Atlas.Chevalley.Integral.Minuscule.TypeC
