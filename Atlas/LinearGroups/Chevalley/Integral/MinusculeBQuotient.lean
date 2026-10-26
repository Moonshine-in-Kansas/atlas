import Atlas.LinearGroups.Chevalley.Integral.MinusculeB
import Atlas.Algebra.CyclicLatticeQuotient

/-! The actual type-B weight/root quotient, with its spin character. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeB
open Classical ClassicalData

def parity (n : ℕ) : WeightLattice (pairingB (n+1)) →ₗ[ℤ] ZMod 2 where
  toFun μ := (μ (corootElement (pairingB (n+1))
    (shortRoot 0 1 (Or.inl rfl))) : ℤ)
  map_add' μ ν := by simp [LinearMap.add_apply]
  map_smul' z μ := by simp [LinearMap.smul_apply]

theorem root_parity (n : ℕ) (a : BRoot (n+1)) :
    parity n (rootWeight (pairingB (n+1)) a) = 0 := by
  change ((coroot (shortRoot (0 : Fin (n+1)) 1 (Or.inl rfl)) a.val : ℤ) : ZMod 2) = 0
  rw [coroot_short]
  simp [show (2 : ZMod 2) = 0 from by decide]

theorem selected_parity (n : ℕ) : parity n (spinWeight n (fun _ => true)) = 1 := by
  change ((spinWeight n (fun _ => true)
    (corootElement (pairingB (n+1)) (shortRoot 0 1 (Or.inl rfl))) : ℤ) : ZMod 2) = 1
  rw [spinWeight_short_pairing]
  norm_num [sign]

theorem rootLattice_le_parity_ker (n : ℕ) :
    rootLattice (pairingB (n+1)) ≤ LinearMap.ker (parity n) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact root_parity n a

theorem rootLattice_sup_selected (n : ℕ) :
    rootLattice (pairingB (n+1)) ⊔
      Submodule.span ℤ {spinWeight n (fun _ => true)} = ⊤ := by
  simpa only [rootLattice, Submodule.span_union] using root_and_spin_weight_span n

theorem selected_double_mem (n : ℕ) :
    (2 : ℤ) • spinWeight n (fun _ => true) ∈ rootLattice (pairingB (n+1)) := by
  have h : (2 : ℤ) • spinWeight n (fun _ => true) =
      ∑ i : Fin (n+1), rootWeight (pairingB (n+1)) (shortRoot i 1 (Or.inl rfl)) := by
    rw [twice_spinWeight]
    ext x
    rw [LinearMap.sum_apply]
    change (∑ i, sign true * x.val (Pi.single i 1)) =
      ∑ i, x.val (Pi.single i 1)
    simp [sign]
  rw [h]
  exact (rootLattice _).sum_mem (fun i _ =>
    (rootWeight_mem_rootLattice _ (shortRoot i 1 (Or.inl rfl))))

theorem rootLattice_eq_parity_ker (n : ℕ) :
    rootLattice (pairingB (n+1)) = LinearMap.ker (parity n) :=
  (Atlas.Algebra.latticeCharacter_ker_eq _ (spinWeight n (fun _ => true)) 2
    (parity n) (rootLattice_le_parity_ker n) (rootLattice_sup_selected n)
    (selected_parity n) (selected_double_mem n)).symm

def weightRootQuotientEquiv (n : ℕ) :
    (WeightLattice (pairingB (n+1)) ⧸ rootLattice (pairingB (n+1))) ≃ₗ[ℤ] ZMod 2 :=
  Atlas.Algebra.cyclicLatticeQuotientEquiv _ (spinWeight n (fun _ => true)) 2
    (parity n) (rootLattice_le_parity_ker n) (rootLattice_sup_selected n)
    (selected_parity n) (selected_double_mem n)

@[simp] theorem weightRootQuotientEquiv_selected (n : ℕ) :
    weightRootQuotientEquiv n (Submodule.Quotient.mk (spinWeight n (fun _ => true))) = 1 :=
  selected_parity n

theorem weightRootQuotient_card (n : ℕ) :
    Nat.card (WeightLattice (pairingB (n+1)) ⧸ rootLattice (pairingB (n+1))) = 2 :=
  Atlas.Algebra.cyclicLatticeQuotient_card _ (spinWeight n (fun _ => true)) 2
    (parity n) (rootLattice_le_parity_ker n) (rootLattice_sup_selected n)
    (selected_parity n) (selected_double_mem n)

end Atlas.Chevalley.Integral.Minuscule.TypeB
