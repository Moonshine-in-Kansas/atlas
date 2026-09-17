import Atlas.Algebra.SymmetricMatrixMetric

noncomputable section
namespace Atlas.Algebra
open scoped BigOperators

/-- Independence of scaled complex squares descends to the actual symmetric
matrices over the embedded field. All scale factors live only in the extension. -/
theorem symmetricMatrixSquare_independent_of_complex {K I J : Type*}
    [Field K] [Fintype I] [Fintype J] (σ : K →+* ℂ)
    (v : J → I → K) (s : I → ℂ)
    (hli : LinearIndependent ℂ (fun j => euclideanSymmetricSquare
      (WithLp.toLp 2 (fun i => σ (v j i) / s i)))) :
    LinearIndependent K (fun j => symmetricMatrixSquare (v j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hz : ∑ j, σ (c j) • euclideanSymmetricSquare
      (WithLp.toLp 2 (fun i => σ (v j i) / s i)) = 0 := by
    apply Subtype.ext
    apply Matrix.ext
    intro i k
    have he := congrArg (fun M : symmetricMatrixSpace K I => M.val i k) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
      symmetricMatrixSquare_apply] at he
    have hh := congrArg σ he
    simp only [map_sum, map_mul, map_zero] at hh
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul]
    change (∑ j, σ (c j) * ((σ (v j i) / s i) * (σ (v j k) / s k))) = 0
    calc
      _ = (∑ j, σ (c j) * (σ (v j i) * σ (v j k))) / (s i * s k) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hh, zero_div]
  have hj := Fintype.linearIndependent_iff.mp hli (fun j => σ (c j)) hz j
  exact σ.injective (by simpa only [map_zero] using hj)

end Atlas.Algebra
