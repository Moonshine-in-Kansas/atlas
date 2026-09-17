import Atlas.Lattices.EisensteinHexadLines
import Atlas.Lattices.EisensteinPhases

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- A heavy hexad coordinate is nonzero precisely on its hexad. -/
theorem eisensteinHexadVector_coordinate_ne (s : Finset (Fin 12))
    (i : Fin 12) (hi : i ∈ s) (j : Fin 12) (hj : j ∈ s) :
    eisensteinHexadVector s i j ≠ 0 := by
  intro he
  have hn := eisensteinHexadVector_coordinate_norm s i hi j
  rw [he] at hn
  by_cases hji : j=i <;> simp [hji,hj] at hn

/-- Coordinate phases preserve a heavy-hexad scalar line exactly when constant on its support. -/
theorem eisensteinHexadVector_phase_line (s : Finset (Fin 12))
    (i : Fin 12) (hi : i ∈ s) (t : TernaryWord) :
    (∃ c : EisensteinRational,
      eisensteinCoordinateEmbedding (eisensteinDiagonal t (eisensteinHexadVector s i)) =
        c • eisensteinCoordinateEmbedding (eisensteinHexadVector s i)) ↔
      ∀ j ∈ s, t j = t i := by
  have hn (j : Fin 12) (hj : j ∈ s) :
      eisensteinToRational (eisensteinHexadVector s i j) ≠ 0 := by
    intro h
    exact eisensteinHexadVector_coordinate_ne s i hi j hj
      (eisensteinToRational_injective (by simpa using h))
  constructor
  · rintro ⟨c,hc⟩ j hj
    have he (k : Fin 12) := congrFun hc k
    have hc' : eisensteinToRational (eisensteinPhase (t i)) = c := by
      apply mul_right_cancel₀ (hn i hi)
      simpa only [eisensteinCoordinateEmbedding,eisensteinDiagonal,LinearMap.coe_mk,
        AddHom.coe_mk,Pi.smul_apply,smul_eq_mul,map_mul] using he i
    apply eisensteinPhase_injective
    apply eisensteinToRational_injective
    apply mul_right_cancel₀ (hn j hj)
    rw [hc']
    simpa only [eisensteinCoordinateEmbedding,eisensteinDiagonal,LinearMap.coe_mk,
      AddHom.coe_mk,Pi.smul_apply,smul_eq_mul,map_mul] using he j
  · intro ht
    refine ⟨eisensteinToRational (eisensteinPhase (t i)),?_⟩
    funext j
    change eisensteinToRational (eisensteinPhase (t j)*eisensteinHexadVector s i j) =
      eisensteinToRational (eisensteinPhase (t i))*eisensteinToRational (eisensteinHexadVector s i j)
    rw [map_mul]
    by_cases hj : j ∈ s
    · rw [ht j hj]
    · have hji : j ≠ i := by intro h; exact hj (h ▸ hi)
      simp [eisensteinHexadVector,eisensteinHexadLift,Pi.smul_apply,hj,hji]

end Atlas.Lattices
