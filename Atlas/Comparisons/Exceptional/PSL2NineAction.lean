import Atlas.LinearGroups.PSLFamily
import Atlas.Comparisons.Exceptional.NineCoordinates
import Atlas.Comparisons.Exceptional.PSL2NineGenerators
import Atlas.Comparisons.Exceptional.TriplePartitions
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

noncomputable section
namespace Atlas.Comparisons.Exceptional.Nine
open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization
abbrev L := ℙ F (Fin 2 → F)

def pointVector : Fin 10 → Fin 2 → F :=
  ![![0,1],![1,1],![2,1],![omega,1],![1+omega,1],![2+omega,1],![2*omega,1],![1+2*omega,1],![2+2*omega,1],![1,0]]
theorem pointVector_ne (i : Fin 10) : pointVector i ≠ 0 := by
  have h : ∀ i : Fin 10, pointVector i ≠ 0 := by decide
  exact h i

def point (i : Fin 10) : L := Projectivization.mk F (pointVector i) (pointVector_ne i)
theorem point_injective : Function.Injective point := by
  intro i j h
  have hd : ∀ i j : Fin 10,
      pointVector i 0 * pointVector j 1 = pointVector j 0 * pointVector i 1 → i = j := by decide
  apply hd i j
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul] at h0 h1
  rw [← h0, ← h1]
  ring

def marking : Fin 10 ≃ L := Equiv.ofBijective point
  ((Nat.bijective_iff_injective_and_card point).mpr ⟨point_injective,by
    rw [Nat.card_fin,Atlas.card_projectiveSpace]
    rw [card]; norm_num⟩)

def permutation : PSL(2,F) →* Equiv.Perm (Fin 10) :=
  marking.symm.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (PSL(2,F)) L)

theorem permutation_injective : Function.Injective permutation := by
  intro g h he
  apply (MulAction.toPerm_injective (β := L))
  exact marking.symm.permCongrHom.injective he

abbrev translation := TriplePartitions.shiftOne
abbrev inversion := TriplePartitions.invert

theorem upper_vector (i : Fin 10) : upperOne.val *ᵥ pointVector i = pointVector (translation i) := by
  have h : ∀ i : Fin 10, upperOne.val *ᵥ pointVector i = pointVector (translation i) := by decide
  exact h i

theorem omega_vector (i : Fin 10) : upperOmega.val *ᵥ pointVector i = pointVector (TriplePartitions.shiftOmega i) := by
  have h : ∀ i : Fin 10, upperOmega.val *ᵥ pointVector i = pointVector (TriplePartitions.shiftOmega i) := by decide
  exact h i

def inversionScale : Fin 10 → F := ![-1,1,2,omega,1+omega,2+omega,2*omega,1+2*omega,2+2*omega,1]
theorem inversion_vector (i : Fin 10) :
    inversionMatrix.val *ᵥ pointVector i = inversionScale i • pointVector (inversion i) := by
  have h : ∀ i : Fin 10, inversionMatrix.val *ᵥ pointVector i =
      inversionScale i • pointVector (inversion i) := by decide
  exact h i

theorem permutation_upper : permutation (upperOne : PSL(2,F)) = translation := by
  apply Equiv.ext
  intro i
  apply marking.injective
  change marking (marking.symm ((upperOne : PSL(2,F)) • marking i)) = _
  rw [marking.apply_symm_apply]
  change (upperOne : PSL(2,F)) • point i = point (translation i)
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,point,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨1, by simpa only [one_smul,Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using (upper_vector i).symm⟩

theorem permutation_inversion : permutation (inversionMatrix : PSL(2,F)) = inversion := by
  apply Equiv.ext
  intro i
  apply marking.injective
  change marking (marking.symm ((inversionMatrix : PSL(2,F)) • marking i)) = _
  rw [marking.apply_symm_apply]
  change (inversionMatrix : PSL(2,F)) • point i = point (inversion i)
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,point,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨inversionScale i, by simpa only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using (inversion_vector i).symm⟩

theorem permutation_omega : permutation (upperOmega : PSL(2,F)) = TriplePartitions.shiftOmega := by
  apply Equiv.ext
  intro i
  apply marking.injective
  change marking (marking.symm ((upperOmega : PSL(2,F)) • marking i)) = _
  rw [marking.apply_symm_apply]
  change (upperOmega : PSL(2,F)) • point i = point (TriplePartitions.shiftOmega i)
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,point,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨1, by simpa only [one_smul,Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using (omega_vector i).symm⟩

end Atlas.Comparisons.Exceptional.Nine
