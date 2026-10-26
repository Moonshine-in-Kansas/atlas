import Atlas.LinearGroups.Chevalley.Comparison.TypeDNaturalElementary
import Atlas.LinearGroups.Chevalley.SelectedOrbitKernelScalar
import Atlas.LinearGroups.Chevalley.Integral.MinusculeDNaturalCoset
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionCenterQuotient
import Atlas.LinearGroups.Orthogonal.ProjectiveElementary

/-! Literal projective descent of the D natural representation over every field.
The adjoint kernel acts by scalar isometries; no equality with the vector kernel,
surjectivity onto the old elementary group, or comparison isomorphism is asserted. -/
noncomputable section
namespace Atlas.Chevalley.Comparison.TypeD
open Classical Atlas.Orthogonal Integral.Minuscule
open scoped _root_.Matrix

theorem rawMatrix_scalar_of_rho_eq_one (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] (g : SelectedWeightCompanion (.D (n+2) hn) K)
    (hg : selectedWeightCompanionRho (.D (n+2) hn) K g=1) :
    ∃ c : Kˣ, rawMatrixHom n hn K g=c.val • (1 : Matrix (Index n) (Index n) K) := by
  classical
  letI : Fintype (WeightOrbit (rootDatum (.D (n+2) hn)).pairing
      (Integral.Minuscule.TypeD.naturalOrbit (n+2))) :=
    Finset.Subtype.fintype (Integral.Minuscule.TypeD.naturalOrbit (n+2))
  obtain ⟨c,hc⟩ := selectedWeightCompanionOrbitRepresentation_scalar_of_rho_eq_one
    (.D (n+2) hn) (Integral.Minuscule.TypeD.naturalOrbit (n+2))
    Integral.Minuscule.TypeD.naturalOrbit_closed Integral.Minuscule.TypeD.naturalOrbit_minuscule K
    (Integral.Minuscule.TypeD.naturalWeight (0 : Fin (n+2)) 1)
    (Integral.Minuscule.TypeD.naturalOrbit_single_rootLattice_coset n) g hg
  refine ⟨c, ?_⟩
  change reindex n K (selectedWeightCompanionOrbitRepresentation (.D (n+2) hn)
    (Integral.Minuscule.TypeD.naturalOrbit (n+2))
    Integral.Minuscule.TypeD.naturalOrbit_closed Integral.Minuscule.TypeD.naturalOrbit_minuscule K g).val = _
  rw [hc]
  change reindex n K (Matrix.diagonal (fun _ : WeightOrbit (ClassicalData.pairingD (n+2))
    (Integral.Minuscule.TypeD.naturalOrbit (n+2)) => c.val)) = _
  have hdiag : (Matrix.diagonal (fun _ : WeightOrbit (ClassicalData.pairingD (n+2))
      (Integral.Minuscule.TypeD.naturalOrbit (n+2)) => c.val)) = c.val • 1 := by
    ext i j
    by_cases h : i=j <;> simp [Matrix.diagonal_apply,Matrix.one_apply,h]
  rw [hdiag,map_smul,map_one]

/-- The scalar square-one conclusion follows from the genuine quadratic form. -/
theorem naturalOrthogonalHom_scalar_of_rho_eq_one (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] (g : SelectedWeightCompanion (.D (n+2) hn) K)
    (hg : selectedWeightCompanionRho (.D (n+2) hn) K g=1) :
    ∃ c : Kˣ, c.val^2=1 ∧ ∀ v, (naturalOrthogonalHom n hn K g).val v=c.val • v := by
  obtain ⟨c,hc⟩ := rawMatrix_scalar_of_rho_eq_one n hn K g hg
  have hscalar (v : Index n → K) :
      (naturalOrthogonalHom n hn K g).val v=c.val • v := by
    rw [naturalOrthogonalHom_apply,hc,Matrix.smul_mulVec,Matrix.one_mulVec]
    change frameEquiv n K (c.val • frameVector n K v)=_
    rw [map_smul]
    exact congrArg (fun w => c.val • w) (frameVector_involutive n K v)
  refine ⟨c, ?_, hscalar⟩
  let v : VectorD (n+2) K := e 0+f 0
  have hv : formD (n+2) K v=1 := by
    simp [v,formD_apply,e,f,Pi.single_apply]
  have hpres := (naturalOrthogonalHom n hn K g).property v
  rw [hscalar,QuadraticMap.map_smul,hv] at hpres
  simpa only [smul_eq_mul,mul_one,pow_two] using hpres

theorem naturalElementaryHom_mem_scalar_of_rho_eq_one (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] (g : SelectedWeightCompanion (.D (n+2) hn) K)
    (hg : selectedWeightCompanionRho (.D (n+2) hn) K g=1) :
    naturalElementaryHom n hn K g ∈ elementaryScalarSubgroup (formD (n+2) K) := by
  obtain ⟨c,hc,hscalar⟩ := naturalOrthogonalHom_scalar_of_rho_eq_one n hn K g hg
  exact ⟨c.val,hc,hscalar⟩

/-- On finite fields the whole selected center maps to scalar isometries.
This is containment in scalars, not identity in the natural representation. -/
theorem naturalElementaryHom_center_mem_scalar (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] [Finite K]
    (g : SelectedWeightCompanion (.D (n+2) hn) K)
    (hg : g ∈ Subgroup.center (SelectedWeightCompanion (.D (n+2) hn) K)) :
    naturalElementaryHom n hn K g ∈ elementaryScalarSubgroup (formD (n+2) K) := by
  apply naturalElementaryHom_mem_scalar_of_rho_eq_one n hn K g
  exact (le_of_eq (selectedWeightCompanion_center_eq_rhoKernel (.D (n+2) hn) K)) hg

def naturalProjectiveHom (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K] :
    SelectedWeightCompanion (.D (n+2) hn) K →* ProjectiveElementary (formD (n+2) K) :=
  (projectiveElementaryMap (formD (n+2) K)).comp (naturalElementaryHom n hn K)

theorem rhoKernel_le_naturalProjectiveKernel (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] :
    (selectedWeightCompanionRho (.D (n+2) hn) K).ker ≤ (naturalProjectiveHom n hn K).ker := by
  intro g hg
  change projectiveElementaryMap (formD (n+2) K) (naturalElementaryHom n hn K g)=1
  exact (QuotientGroup.eq_one_iff _).mpr
    (naturalElementaryHom_mem_scalar_of_rho_eq_one n hn K g hg)

/-- The actual adjoint Model maps to the old projective elementary group.
Descent uses the proved rho-kernel inclusion and actual rho surjectivity. -/
def modelNaturalProjectiveHom (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K] :
    Model (.D (n+2) hn) K →* ProjectiveElementary (formD (n+2) K) :=
  (QuotientGroup.lift (selectedWeightCompanionRho (.D (n+2) hn) K).ker
    (naturalProjectiveHom n hn K) (rhoKernel_le_naturalProjectiveKernel n hn K)).comp
      (QuotientGroup.quotientKerEquivOfSurjective (selectedWeightCompanionRho (.D (n+2) hn) K)
        (selectedWeightCompanionRho_surjective (.D (n+2) hn) K)).symm.toMonoidHom

theorem modelNaturalProjectiveHom_rho (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (g : SelectedWeightCompanion (.D (n+2) hn) K) :
    modelNaturalProjectiveHom n hn K (selectedWeightCompanionRho (.D (n+2) hn) K g) =
      naturalProjectiveHom n hn K g := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (selectedWeightCompanionRho (.D (n+2) hn) K)
    (selectedWeightCompanionRho_surjective (.D (n+2) hn) K)
  have he : e (QuotientGroup.mk g)=selectedWeightCompanionRho (.D (n+2) hn) K g := rfl
  change QuotientGroup.lift (selectedWeightCompanionRho (.D (n+2) hn) K).ker
    (naturalProjectiveHom n hn K) (rhoKernel_le_naturalProjectiveKernel n hn K)
    (e.symm (selectedWeightCompanionRho (.D (n+2) hn) K g)) = _
  rw [← he,e.symm_apply_apply]
  rfl

theorem modelNaturalProjectiveHom_X (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+2)) (t : K) :
    modelNaturalProjectiveHom n hn K (modelX (.D (n+2) hn) K i t) =
      naturalProjectiveHom n hn K (selectedWeightCompanionX (.D (n+2) hn) K i t) := by
  change modelNaturalProjectiveHom n hn K
    (selectedWeightCompanionRho (.D (n+2) hn) K
      (selectedWeightCompanionX (.D (n+2) hn) K i t)) = _
  exact modelNaturalProjectiveHom_rho n hn K _

theorem modelNaturalProjectiveHom_Y (n : ℕ) (hn : 4≤n+2) (K : Type*) [Field K]
    (i : Fin (n+2)) (t : K) :
    modelNaturalProjectiveHom n hn K (modelY (.D (n+2) hn) K i t) =
      naturalProjectiveHom n hn K (selectedWeightCompanionY (.D (n+2) hn) K i t) := by
  change modelNaturalProjectiveHom n hn K
    (selectedWeightCompanionRho (.D (n+2) hn) K
      (selectedWeightCompanionY (.D (n+2) hn) K i t)) = _
  exact modelNaturalProjectiveHom_rho n hn K _

/-- A marked root element survives projectivization, even over the binary field. -/
theorem modelNaturalProjectiveHom_X_one_ne_one (n : ℕ) (hn : 4≤n+2)
    (K : Type*) [Field K] :
    modelNaturalProjectiveHom n hn K (modelX (.D (n+2) hn) K (0 : Fin (n+2)) 1) ≠ 1 := by
  intro h
  rw [modelNaturalProjectiveHom_X] at h
  have hs := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨c,_,hc⟩ := hs
  have he := congrFun (hc (e ((0 : Fin (n+1)).succ))) (.inl ((0 : Fin (n+1)).castSucc))
  change (naturalOrthogonalHom n hn K
    (selectedWeightCompanionX (.D (n+2) hn) K ((0 : Fin (n+1)).castSucc) 1)).val
      (e ((0 : Fin (n+1)).succ)) (.inl ((0 : Fin (n+1)).castSucc)) = _ at he
  rw [naturalOrthogonalHom_apply,matrix_X_pair] at he
  simpa [frameVector,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
    Matrix.single_mulVec,Function.update_apply,e,Pi.single_apply,smul_eq_mul] using he

end Atlas.Chevalley.Comparison.TypeD
