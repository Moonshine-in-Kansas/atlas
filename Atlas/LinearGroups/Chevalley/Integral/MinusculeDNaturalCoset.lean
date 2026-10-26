import Atlas.LinearGroups.Chevalley.Integral.MinusculeDNatural

/-! All signed natural D weights lie in one literal root-lattice coset.
The equal-coordinate case uses two actual roots through a distinct coordinate;
there is no division by two and no coefficient-field assumption. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.TypeD
open Classical ClassicalData

theorem naturalWeight_sub_eq_rootWeight {r : ℕ} (i j : Fin r) (hij : i≠j)
    (s t : ℤ) (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1) :
    naturalWeight i s-naturalWeight j t = rootWeight (pairingD r)
      (longRoot false i j hij s (-t) hs (by rcases ht with rfl | rfl <;> simp)) := by
  have hsingle (k : Fin r) (a : ℤ) :
      (Pi.single k a : ClassicalData.Lattice r)=a • Pi.single k 1 := by
    ext l
    by_cases h : l=k <;> simp [Pi.single_apply,h,eq_comm]
  ext x
  change x.val (s • (Pi.single i 1 : ClassicalData.Lattice r))-
    x.val (t • (Pi.single j 1 : ClassicalData.Lattice r)) =
      x.val (Pi.single i s+Pi.single j (-t))
  rw [hsingle i s,hsingle j (-t)]
  simp only [map_add,map_smul,smul_eq_mul]
  ring

theorem naturalWeight_sub_mem_rootLattice (n : ℕ) (i j : Fin (n+2))
    (s t : ℤ) (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1) :
    naturalWeight i s-naturalWeight j t ∈ rootLattice (pairingD (n+2)) := by
  by_cases hij : i=j
  · subst j
    obtain ⟨k,hki⟩ := exists_ne i
    have h₁ : naturalWeight i s-naturalWeight k 1 ∈ rootLattice (pairingD (n+2)) := by
      rw [naturalWeight_sub_eq_rootWeight i k (Ne.symm hki) s 1 hs (Or.inl rfl)]
      exact rootWeight_mem_rootLattice _ _
    have h₂ : naturalWeight k 1-naturalWeight i t ∈ rootLattice (pairingD (n+2)) := by
      rw [naturalWeight_sub_eq_rootWeight k i hki 1 t (Or.inl rfl) ht]
      exact rootWeight_mem_rootLattice _ _
    convert (rootLattice (pairingD (n+2))).add_mem h₁ h₂ using 1 <;> abel
  · rw [naturalWeight_sub_eq_rootWeight i j hij s t hs ht]
    exact rootWeight_mem_rootLattice _ _

theorem naturalOrbit_single_rootLattice_coset (n : ℕ)
    (μ : WeightLattice (pairingD (n+2))) (hμ : μ ∈ naturalOrbit (n+2)) :
    μ-naturalWeight (0 : Fin (n+2)) 1 ∈ rootLattice (pairingD (n+2)) := by
  obtain ⟨⟨i,s⟩,_,rfl⟩ := Finset.mem_image.mp hμ
  apply naturalWeight_sub_mem_rootLattice n i 0 (sign s) 1 _ (Or.inl rfl)
  cases s <;> simp [sign]

end Atlas.Chevalley.Integral.Minuscule.TypeD
