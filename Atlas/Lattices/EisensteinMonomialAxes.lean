import Atlas.Lattices.EisensteinMonomial

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- The intersection of the integral lattice with each coordinate axis is exactly 3θE. -/
theorem eisensteinLeechModule_axis_iff (i : Fin 12) (c : Eisenstein) :
    Pi.single i c ∈ eisensteinLeechModule ↔ 3*eisensteinTheta ∣ c := by
  constructor
  · rintro ⟨m,hm⟩
    obtain ⟨j,hji⟩ := exists_ne i
    have hmres : eisensteinResidue m = 0 := by
      have hh := eisensteinCongruence_residue _ m hm j
      simpa [Pi.single_apply,hji] using hh.symm
    have hzero := eisensteinLeechModule_common_lift (Pi.single i c) ⟨m,hm⟩ 0 (fun k => by
      rw [eisensteinCongruence_residue _ m hm k,hmres,map_zero])
    obtain ⟨_,_,_,hs⟩ := hzero
    simpa using hs
  · rintro ⟨d,rfl⟩
    have h := eisensteinLeechModule_contains_multiple (Pi.single i d)
    have he : (3*eisensteinTheta) • Pi.single i d = Pi.single i ((3*eisensteinTheta)*d) := by
      funext j
      by_cases hj : j=i <;> simp [Pi.single_apply,Pi.smul_apply,hj]
    rw [he] at h; exact h

/-- The same exact axis intersection in the rational scalar realization. -/
theorem rationalEisensteinLattice_axis_iff (i : Fin 12) (a : EisensteinRational) :
    Pi.single i a ∈ rationalEisensteinLattice ↔
      ∃ d : Eisenstein, a = eisensteinToRational (3*eisensteinTheta) * eisensteinToRational d := by
  constructor
  · rintro ⟨z,hz,he⟩
    have hi : eisensteinToRational (z i) = a := by
      have hh := congrFun he i
      simpa [eisensteinCoordinateEmbedding] using hh
    have hzaxis : z = Pi.single i (z i) := by
      funext j
      by_cases hj : j=i
      · subst j; simp
      · have hh := congrFun he j
        have hzero : eisensteinToRational (z j) = 0 := by
          simpa [eisensteinCoordinateEmbedding,Pi.single_apply,hj] using hh
        have hzi : z j=0 := eisensteinToRational_injective (hzero.trans (map_zero _).symm)
        simp [Pi.single_apply,hj,hzi]
    have hc : 3*eisensteinTheta ∣ z i :=
      (eisensteinLeechModule_axis_iff i (z i)).mp (hzaxis ▸ hz)
    obtain ⟨d,hd⟩ := hc
    exact ⟨d,by rw [← hi,hd,map_mul]⟩
  · rintro ⟨d,rfl⟩
    refine ⟨Pi.single i ((3*eisensteinTheta)*d),
      (eisensteinLeechModule_axis_iff _ _).mpr (dvd_mul_right _ _),?_⟩
    funext j
    by_cases hj : j=i <;> simp [eisensteinCoordinateEmbedding,Pi.single_apply,hj]

theorem eisensteinAxisScale_ne_zero : eisensteinToRational (3*eisensteinTheta) ≠ 0 := by
  intro h
  have hh := congrArg QuadraticAlgebra.re h
  norm_num [eisensteinToRational,eisensteinTheta,eisensteinOmega,QuadraticAlgebra.omega] at hh

/-- Axis-lattice preservation and a norm-one coefficient force an integral unit.
This closes the coefficient-integrality step for a monomial Hermitian isometry. -/
theorem eisensteinAxis_isometry_coefficient_unit (i : Fin 12) (a : EisensteinRational)
    (ha : star a*a = 1)
    (hl : Pi.single i (a*eisensteinToRational (3*eisensteinTheta)) ∈ rationalEisensteinLattice) :
    ∃ u : Eisensteinˣ, eisensteinToRational (u : Eisenstein) = a := by
  obtain ⟨d,hd⟩ := (rationalEisensteinLattice_axis_iff i _).mp hl
  have he : a = eisensteinToRational d := by
    apply mul_left_cancel₀ eisensteinAxisScale_ne_zero
    simpa [mul_comm] using hd
  have hn : d.norm = 1 := by
    have hreal := congrArg eisensteinReal ha
    rw [he,eisensteinReal_star_mul_self] at hreal
    have heq : (d.re : ℚ)^2 - (d.re : ℚ)*(d.im : ℚ) + (d.im : ℚ)^2 = 1 := by
      simpa [eisensteinToRational,eisensteinReal] using hreal
    rw [eisenstein_norm]
    exact_mod_cast heq
  obtain ⟨u,hu⟩ := (eisenstein_isUnit_iff d).mpr hn
  exact ⟨u,by rw [hu]; exact he.symm⟩

end Atlas.Lattices
