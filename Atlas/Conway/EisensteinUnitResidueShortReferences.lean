import Atlas.Conway.EisensteinUnitResidueFrames

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def eisensteinShortSingletonCorrection (b : Bool) : Eisenstein :=
  if b then eisensteinOmega else eisensteinOmega^2

theorem eisensteinShortSingletonCorrection_residue (b : Bool) :
    eisensteinResidue (eisensteinShortSingletonCorrection b)=1 := by
  cases b <;> decide +kernel

theorem eisensteinShortSingletonCorrection_norm (b : Bool) :
    (1+3*eisensteinShortSingletonCorrection b).norm=7 := by
  cases b <;> decide +kernel

def eisensteinShortSingletonLattice (i : Fin 12) (b : Bool) : EisensteinLattice :=
  ⟨fun j => 1+3*(Pi.single i (eisensteinShortSingletonCorrection b) : EisensteinCoordinates) j,
    eisensteinOneModThree_mem _ (by
      rw [Finset.sum_pi_single', if_pos (Finset.mem_univ i), ← eisensteinResidue_eq_zero]
      rw [map_add, eisensteinShortSingletonCorrection_residue]
      decide +kernel)⟩

theorem eisensteinShortSingleton_norm (i : Fin 12) (b : Bool) :
    eisensteinNorm (eisensteinShortSingletonLattice i b)=4 := by
  have hc (j : Fin 12) :
      (1+3*(Pi.single i (eisensteinShortSingletonCorrection b) : EisensteinCoordinates) j).norm =
      1+6*(Pi.single i (1 : ℤ) : Fin 12 → ℤ) j := by
    by_cases hj : j=i
    · subst j
      simpa only [Pi.single_eq_same, mul_one, show (1+6 : ℤ)=7 by decide] using eisensteinShortSingletonCorrection_norm b
    · simp [Pi.single_apply,hj]
  unfold eisensteinNorm
  rw [eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ)*(∑ j, (eisensteinToRational
    (1+3*(Pi.single i (eisensteinShortSingletonCorrection b) : EisensteinCoordinates) j)).norm)=4
  simp_rw [eisensteinToRational_norm,hc]
  push_cast
  norm_num [Finset.sum_add_distrib,← Finset.mul_sum,Pi.single_apply]

def eisensteinShortPairLattice (i j : Fin 12) : EisensteinLattice :=
  ⟨fun k => 1+3*((-Pi.single i 1-Pi.single j 1 : EisensteinCoordinates) k),
    eisensteinOneModThree_mem _ (by
      simp only [Pi.sub_apply,Pi.neg_apply,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
        Finset.sum_pi_single',Finset.mem_univ,ite_true]
      rw [← eisensteinResidue_eq_zero]
      decide +kernel)⟩

theorem eisensteinShortPair_norm (i j : Fin 12) (hij : i ≠ j) :
    eisensteinNorm (eisensteinShortPairLattice i j)=4 := by
  have hc (k : Fin 12) :
      (1+3*((-Pi.single i 1-Pi.single j 1 : EisensteinCoordinates) k)).norm =
      1+3*(Pi.single i (1 : ℤ) : Fin 12 → ℤ) k+
        3*(Pi.single j (1 : ℤ) : Fin 12 → ℤ) k := by
    by_cases hi : k=i <;> by_cases hj : k=j
    · exact False.elim (hij (hi.symm.trans hj))
    · simp [Pi.single_apply,hi,hj,hij,Ne.symm hij,show (1+3*(-1) : Eisenstein).norm=4 by decide +kernel]
      decide +kernel
    · simp [Pi.single_apply,hi,hj,hij,Ne.symm hij,show (1-3 : Eisenstein).norm=4 by decide +kernel]
      decide +kernel
    · simp [Pi.single_apply,hi,hj]
  unfold eisensteinNorm
  rw [eisensteinBilinear_self_sum_norm]
  change (2/9 : ℚ)*(∑ k, (eisensteinToRational
    (1+3*((-Pi.single i 1-Pi.single j 1 : EisensteinCoordinates) k))).norm)=4
  simp_rw [eisensteinToRational_norm,hc]
  push_cast
  norm_num [Finset.sum_add_distrib,← Finset.mul_sum,Pi.single_apply]

/-- A norm-six normalized vector cannot occupy the syndrome and integral-sum
lift represented by an actual norm-four lattice vector. -/
theorem eisensteinOneModThree_short_excluded (x : EisensteinShell 6)
    (y : EisensteinShell 4) (a b : EisensteinCoordinates)
    (ha : ∀ j, x.val.val j=1+3*a j) (hb : ∀ j, y.val.val j=1+3*b j)
    (hc : eisensteinWordResidue (a-b) ∈ ternaryGolay) :
    ¬ (3 : Eisenstein) ∣ ∑ j, (a-b) j := by
  intro hd
  exact eisenstein_four_six_differentClass y.val x.val y.property x.property
    ((eisensteinOneModThree_class_iff x.val y.val a b ha hb).mpr ⟨hc,hd⟩).symm

end Atlas.Conway
