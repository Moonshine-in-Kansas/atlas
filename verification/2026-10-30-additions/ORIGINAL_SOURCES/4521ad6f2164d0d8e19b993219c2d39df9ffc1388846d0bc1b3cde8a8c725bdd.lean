import Atlas.LinearGroups.SuzukiFamily.TensorAction
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Uniform diagonal reduction after matching two opposite ovoid points.
Only two partial-tensor column relations are needed beyond symplecticity. -/
noncomputable section
namespace Atlas.SuzukiFamily
open scoped Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem tensor_matrix_diagonal_reduction (m : ℕ)
    (A : Matrix (Fin 4) (Fin 4) F) (a d : Fˣ)
    (h0 : ∀ i, A i 0 = if i=0 then (a:F) else 0)
    (h3 : ∀ i, A i 3 = if i=3 then (d:F) else 0)
    (hB : ∀ i j, tensorPolar (fun k => A k i) (fun k => A k j) =
      if (i:ℕ)+(j:ℕ)=3 then 1 else 0)
    (h01 : rawPartialTensor (fun k => A k 0) (fun k => A k 1) =
      fun i => theta F m (A i 0))
    (h02 : rawPartialTensor (fun k => A k 0) (fun k => A k 2) =
      fun i => theta F m (A i 1)) : ∃ t : Fˣ, A = h m t := by
  have h11 : A 0 1=0 := by
    have hh := hB 3 1
    have hh' : (d:F)*A 0 1=0 := by simpa [tensorPolar,h3] using hh
    exact (mul_eq_zero.mp hh').resolve_left d.ne_zero
  have h12 : A 3 1=0 := by
    have hh := hB 0 1
    simpa [tensorPolar,h0] using hh
  have h21 : A 0 2=0 := by
    have hh := hB 3 2
    simpa [tensorPolar,h3] using hh
  have h22 : A 3 2=0 := by
    have hh := hB 0 2
    simpa [tensorPolar,h0] using hh
  have hz21 : A 2 1=0 := by
    have hh := congrFun h01 1
    have hh' : (a:F)*A 2 1=0 := by simpa [rawPartialTensor,h0] using hh
    exact (mul_eq_zero.mp hh').resolve_left a.ne_zero
  have hz12 : A 1 2=0 := by
    have hh := congrFun h02 0
    have hh' : (a:F)*A 1 2=0 := by simpa [rawPartialTensor,h0,h11] using hh
    exact (mul_eq_zero.mp hh').resolve_left a.ne_zero
  let diag : Fin 4 → F := ![(a:F),A 1 1,A 2 2,(d:F)]
  have h03 : diag 0*diag 3=1 := by simpa [diag,tensorPolar,h0,h3] using hB 0 3
  have hdiag12 : diag 1*diag 2=1 := by
    simpa [diag,tensorPolar,h11,h12,h21,h22,hz21,hz12] using hB 1 2
  have ht : theta F m (diag 1)=diag 0*diag 2 := by
    simpa [diag,rawPartialTensor,h0] using (congrFun h02 1).symm
  obtain ⟨t,ht⟩ := tensor_diagonal_parameters diag h03 hdiag12 ht
  refine ⟨t,?_⟩
  have hA : A=Matrix.diagonal diag := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal,diag,h0,h3,h11,h12,h21,h22,hz21,hz12]
  rw [hA,ht]
  rfl


theorem tensor_linear_diagonal_reduction (m : ℕ)
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (a d : Fˣ)
    (h0 : g (tensorBasis 0)=a • tensorBasis 0)
    (h3 : g (tensorBasis 3)=d • tensorBasis 3)
    (hB : ∀ x y, tensorPolar (g x) (g y)=tensorPolar x y)
    (hT : PreservesPartialTensor m g) :
    ∃ t : Fˣ, ∀ v, g v=h m t *ᵥ v := by
  let A := LinearMap.toMatrix' g.toLinearMap
  have hA (i j : Fin 4) : A i j=g (tensorBasis j) i := rfl
  have hA0 (i : Fin 4) : A i 0=if i=0 then (a:F) else 0 := by
    rw [hA,h0]
    simp [tensorBasis,Pi.single_apply,Units.smul_def]
  have hA3 (i : Fin 4) : A i 3=if i=3 then (d:F) else 0 := by
    rw [hA,h3]
    simp [tensorBasis,Pi.single_apply,Units.smul_def]
  have hAB (i j : Fin 4) : tensorPolar (fun k => A k i) (fun k => A k j)=
      if (i:ℕ)+(j:ℕ)=3 then 1 else 0 := by
    simp only [hA,hB]
    fin_cases i <;> fin_cases j <;> norm_num [tensorPolar,tensorBasis,Pi.single_apply,Fin.ext_iff]
  obtain ⟨t,ht⟩ := tensor_matrix_diagonal_reduction m A a d hA0 hA3 hAB
    (partialTensor_preserves_column01 g hT) (partialTensor_preserves_column02 g hT)
  refine ⟨t,?_⟩
  intro v
  have hv : A *ᵥ v=g v := LinearMap.toMatrix'_mulVec g.toLinearMap v
  rw [ht] at hv
  exact hv.symm

end Atlas.SuzukiFamily
