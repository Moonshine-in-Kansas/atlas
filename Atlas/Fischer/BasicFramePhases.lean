import Atlas.Fischer.ReflectingRootBasicSupport
import Atlas.Fischer.IntrinsicTraceForm
import Atlas.Fischer.RootRays

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The nonzero pairings between marked basic roots force a single scalar phase. -/
theorem basicFrame_common_phase (e : SemilinearAlgebraAutomorphism)
    (σ : Equiv.Perm Omega)
    (hσ : ∀ i, rootRay (e.val (basicAxis i)) = rootRay (basicAxis (σ i))) :
    ∃ a : Mu3, ∀ i, e.val (basicAxis i) = a.val.val • basicAxis (σ i) := by
  classical
  choose a ha using fun i => (rootRay_eq_iff_mu3 _ _).mp (hσ i)
  have heq (i j : Omega) : (a i).val.val = (a j).val.val := by
    by_cases hij : i = j
    · subst j; rfl
    have h := semilinearAlgebraAutomorphism_hermitian e (basicAxis i) (basicAxis j)
    rw [ha i, ha j, hermitian_smul_left, hermitian_smul_right,
      hermitian_basicAxis_basicAxis, hermitian_basicAxis_basicAxis] at h
    simp only [hij, σ.injective.ne hij, ite_false, map_one, mul_one] at h
    have hn := cube_root_unit_norm ((mem_rootsOfUnity' _ _).mp (a j).property)
    have hn' : (a j).val.val * star (a j).val.val = 1 := by simpa only [mul_comm] using hn
    have hne : star (a j).val.val ≠ 0 := star_ne_zero.mpr (a j).val.ne_zero
    exact mul_right_cancel₀ hne (h.trans hn'.symm)
  let i : Omega := Classical.choice inferInstance
  refine ⟨a i, fun j => ?_⟩
  rw [ha j, heq j i]

end Atlas.Fischer
