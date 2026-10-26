import Atlas.Lattices.ConwayWales.CodeSeedCoordinates
import Atlas.LinearAlgebra.DoubledCoordinates
import Atlas.LinearAlgebra.PivotRows

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open scoped Matrix

def realBlockEquiv : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv

abbrev EightCoordinates := Fin 8 → ZMod 4

def codeZeroEvaluation : FrameCodeSpace →ₗ[ZMod 4] EightCoordinates where
  toFun c j := ∑ r : Row, c (r, realBlockEquiv.symm j)
  map_add' c d := by ext j; exact Finset.sum_add_distrib
  map_smul' a c := by ext j; exact (Finset.mul_sum _ _ _).symm

def zeroComponentCode : Submodule (ZMod 4) EightCoordinates :=
  frameCodeModule.map codeZeroEvaluation

def zeroComponentRows : Matrix (Fin 7) (Fin 8) (ZMod 4) :=
  ![![1,-1,1,1,1,1,1,1], ![0,1,1,0,1,0,1,0],
    ![0,0,1,0,0,0,0,1], ![0,0,0,1,0,0,1,0],
    ![0,0,0,0,1,0,0,1], ![0,0,0,0,0,1,1,0], ![0,0,0,0,0,0,1,1]]

def zeroComponentCoefficients : Matrix (Fin 7) (Fin 8) (ZMod 4) :=
  ![![1,0,0,0,0,0,0,0], ![-1,1,0,0,0,0,0,0],
    ![2,-1,0,0,1,0,0,0], ![-1,0,0,0,0,1,0,0],
    ![-1,0,0,1,0,0,0,0], ![2,-1,1,0,0,0,0,0], ![0,-1,0,-1,0,-1,1,0]]

def zeroComponentWitness (i : Fin 7) : FrameCodeSpace :=
  ∑ j : Fin 8, zeroComponentCoefficients i j •
    modFour (integerCodeSeed 0 (realBlockEquiv.symm j).1 (realBlockEquiv.symm j).2)

theorem zeroComponentWitness_mem (i : Fin 7) : zeroComponentWitness i ∈ frameCodeModule := by
  unfold zeroComponentWitness
  apply Submodule.sum_mem
  intro j _
  exact frameCodeModule.smul_mem _ (integerCodeSeed_mem _ _ _)

/-- Appendix A's seven row identities in the linear component, checked in Z/4. -/
theorem zeroComponentWitness_evaluation : ∀ i : Fin 7,
    codeZeroEvaluation (zeroComponentWitness i) =
      (if i = 0 then (1 : ZMod 4) else 2) • zeroComponentRows i := by
  decide

theorem zeroComponentRows_mem (i : Fin 7) :
    (if i = 0 then (1 : ZMod 4) else 2) • zeroComponentRows i ∈ zeroComponentCode := by
  rw [← zeroComponentWitness_evaluation]
  exact ⟨_,zeroComponentWitness_mem i,rfl⟩

theorem zeroComponentRows_triangular :
    (zeroComponentRows.submatrix id (fun i : Fin 7 => i.castSucc)).IsUpperTriangular := by
  decide

theorem zeroComponentRows_diagonal (i : Fin 7) : zeroComponentRows i i.castSucc = 1 := by
  revert i
  decide

abbrev ZeroComponentParameters := ZMod 4 × (Fin 6 → Atlas.LinearAlgebra.Doubled (ZMod 4))

def zeroComponentParameterCoefficients (p : ZeroComponentParameters) : Fin 7 → ZMod 4 :=
  Fin.cons p.1 (fun i => (p.2 i).val)

theorem zeroComponentParameterCoefficients_injective :
    Function.Injective zeroComponentParameterCoefficients := by
  intro p q h
  apply Prod.ext
  · exact congrFun h 0
  · funext i
    apply Subtype.ext
    exact congrFun h i.succ

theorem zeroComponent_combinations_mem (p : ZeroComponentParameters) :
    zeroComponentParameterCoefficients p ᵥ* zeroComponentRows ∈ zeroComponentCode := by
  change (∑ i : Fin 7, zeroComponentParameterCoefficients p i • zeroComponentRows i) ∈ zeroComponentCode
  apply Submodule.sum_mem
  intro i _
  cases i using Fin.cases with
  | zero =>
    apply zeroComponentCode.smul_mem
    simpa only [ite_true, one_smul] using zeroComponentRows_mem 0
  | succ i =>
    obtain ⟨y,hy⟩ := (p.2 i).property
    have hr : (2 : ZMod 4) • zeroComponentRows i.succ ∈ zeroComponentCode := by
      simpa only [Fin.succ_ne_zero, ite_false] using zeroComponentRows_mem i.succ
    convert zeroComponentCode.smul_mem y hr using 1
    funext j
    change (p.2 i).val * zeroComponentRows i.succ j = y * (2 * zeroComponentRows i.succ j)
    rw [← hy, nsmul_eq_mul]
    ring

theorem zeroComponent_card_lower_bound : 256 ≤ Nat.card zeroComponentCode := by
  letI : Finite (Atlas.LinearAlgebra.Doubled (ZMod 4)) := by
    unfold Atlas.LinearAlgebra.Doubled
    infer_instance
  have hdet : IsUnit (zeroComponentRows.submatrix id (fun i : Fin 7 => i.castSucc)).det := by
    rw [Matrix.det_of_isUpperTriangular zeroComponentRows_triangular]
    simpa only [Matrix.submatrix_apply, id_eq, zeroComponentRows_diagonal, Finset.prod_const_one]
      using (isUnit_one : IsUnit (1 : ZMod 4))
  have h := Atlas.LinearAlgebra.pivotRows_card_le zeroComponentCode zeroComponentRows
    (fun i : Fin 7 => i.castSucc) hdet zeroComponentParameterCoefficients
    zeroComponentParameterCoefficients_injective zeroComponent_combinations_mem
  have hp : Nat.card ZeroComponentParameters = 256 := by
    simp [Nat.card_prod, Nat.card_fun, Atlas.LinearAlgebra.doubled_zmod_four_card]
  rwa [hp] at h

end Atlas.ConwayWales

