import Atlas.LinearGroups.Triality.AbsoluteRoots

noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable {K : Type*} [Field K]

theorem negativeSumRoot_add {n : ℕ} (i j : Fin n) (s t : K) :
    negativeSumRoot i j (s+t) = negativeSumRoot i j s * negativeSumRoot i j t := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change Atlas.Quadratic.siegel _ _ ((s+t) • f i) x =
    Atlas.Quadratic.siegel _ _ (s • f i) (Atlas.Quadratic.siegel _ _ (t • f i) x)
  rw [Atlas.Quadratic.siegel_add _ _ _ _ _ (formD_f j) (by rw [map_smul, polarD_f]; simp [f])
    (by rw [map_smul, polarD_f]; simp [f]), add_smul]

theorem pinnedRoot_add (i : Fin 4) (s t : K) :
    pinnedRoot i (s+t) = pinnedRoot i s * pinnedRoot i t := by
  fin_cases i
  · exact differenceRoot_add 0 1 (by decide) s t
  · exact differenceRoot_add 1 2 (by decide) s t
  · exact differenceRoot_add 2 3 (by decide) s t
  · exact sumRoot_add 2 3 s t

theorem pinnedNegativeRoot_add (i : Fin 4) (s t : K) :
    pinnedNegativeRoot i (s+t) = pinnedNegativeRoot i s * pinnedNegativeRoot i t := by
  fin_cases i
  · exact differenceRoot_add 1 0 (by decide) s t
  · exact differenceRoot_add 2 1 (by decide) s t
  · exact differenceRoot_add 3 2 (by decide) s t
  · exact negativeSumRoot_add 2 3 s t

@[simp] theorem pinnedRoot_zero (i : Fin 4) : pinnedRoot i (0 : K) = 1 := by
  have h := pinnedRoot_add i (0 : K) 0
  exact (mul_eq_left.mp (show pinnedRoot i (0 : K) * pinnedRoot i 0 = pinnedRoot i 0 by
    simpa only [add_zero] using h.symm))

@[simp] theorem pinnedNegativeRoot_zero (i : Fin 4) : pinnedNegativeRoot i (0 : K) = 1 := by
  have h := pinnedNegativeRoot_add i (0 : K) 0
  exact (mul_eq_left.mp (show pinnedNegativeRoot i (0 : K) * pinnedNegativeRoot i 0 = pinnedNegativeRoot i 0 by
    simpa only [add_zero] using h.symm))

end Atlas.Triality
