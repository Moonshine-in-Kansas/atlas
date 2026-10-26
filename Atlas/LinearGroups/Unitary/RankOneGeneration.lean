import Atlas.LinearGroups.Unitary.RankOneProjective
import Atlas.LinearGroups.Unitary.PointNormalClosure
import Atlas.LinearGroups.Unitary.PerfectThree

/-! Positive rank-one generation through the actual SL₂ comparison. -/
noncomputable section
namespace Atlas.Unitary
open Atlas.FiniteQuadratic
open scoped MatrixGroups
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem special_two_perfect (hdeg : Module.finrank F K = 2) (hq : 4 ≤ Nat.card F) :
    Group.IsPerfect (SU F K 2 hdeg) := by
  obtain ⟨a,ha⟩ := exists_pow_ne_one_of_isCyclic (G := Fˣ) (k := 2) (by decide)
    (by rw [Nat.card_units]; omega)
  have ha' : (a : F)^2 ≠ 1 := fun h => ha (Units.ext (by simpa using h))
  letI : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top a.ne_zero ha'⟩
  exact Group.IsPerfect.ofSurjective (f := (specialUnitaryTwoEquiv hdeg).toMonoidHom)
    (specialUnitaryTwoEquiv hdeg).surjective

theorem transvectionGenerated_two_eq_top_of_four_le (hdeg : Module.finrank F K = 2)
    (hq : 4 ≤ Nat.card F) : transvectionGenerated hdeg (n := 2) = ⊤ := by
  let H := transvectionGenerated hdeg (n := 2)
  let π := projection F K 2 hdeg
  let N := H.map π
  letI : N.Normal := (inferInstance : H.Normal).map π (projection_surjective F K 2 hdeg)
  letI := (psu_two_simple_iff hdeg).mpr (show Nat.card F ≠ 2 ∧ Nat.card F ≠ 3 by omega)
  have hN : N = ⊤ := by
    rcases (inferInstance : N.Normal).eq_bot_or_eq_top with h | h
    · obtain ⟨a,b,ha,hb⟩ := exists_witt_parameters hdeg
      let v : Fin 2 → K := ![1,a]
      have hv : v ≠ 0 := by intro he; have := congrFun he 0; simpa [v] using this
      have hvv : hermitian F K v v = 0 := by simp [v,hermitian,Fin.sum_univ_succ,ha]
      let p := isotropicPoint v hv hvv
      have hle : projectivePointTransvections hdeg p ≤ N :=
        Subgroup.map_mono (pointTransvections_le_generated hdeg p)
      rw [h] at hle
      have hbot := bot_unique hle
      have hc := card_projectivePointTransvections hdeg (by decide : 0 < 2) p
      rw [hbot] at hc
      have hf : Nat.card F = 1 := by simpa using hc.symm
      omega
    · exact h
  have ht : H ⊔ Subgroup.center (SU F K 2 hdeg) = ⊤ := by
    rw [← projection_kernel F K 2 hdeg, ← Subgroup.comap_map_eq]
    change N.comap π = ⊤
    rw [hN,Subgroup.comap_top]
  have hle := (inferInstance : H.Normal).commutator_le_of_self_sup_commutative_eq_top ht inferInstance
  letI := special_two_perfect hdeg hq
  rw [Group.IsPerfect.commutator_eq_top] at hle
  exact top_unique hle
end Atlas.Unitary
