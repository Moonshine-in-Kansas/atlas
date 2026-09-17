import Atlas.LinearGroups.Orthogonal.SpinorNorm
import Atlas.LinearGroups.Orthogonal.ReflectionConjugation
import Atlas.LinearAlgebra.InvolutionEigenspaceRestrictions
import Atlas.LinearAlgebra.QuadraticFiniteRepresentation

/-! # Determinant and spinor correction inside an involution centralizer -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic Atlas.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

/-- Reflection in either eigenspace of an involution centralizes that involution. -/
theorem reflectionElement_commute_of_minus (t : isometrySubgroup Q) (a : V)
    (ha : Q a ≠ 0) (hta : t.val a = -a) :
    Commute t (reflectionElement Q a ha) := by
  apply (mul_inv_eq_iff_eq_mul).mp
  have hc := reflectionElement_conj Q t a ha
  have he : reflectionElement Q (t.val a)
      (by exact ne_of_eq_of_ne ((isometryCarrierEquiv Q t).map_app a) ha) =
      reflectionElement Q a ha := by
    convert reflectionElement_smul Q a ha (-1) (neg_ne_zero.mpr one_ne_zero) using 1 <;>
      simp only [hta, neg_one_smul]
  exact hc.trans he

variable [FiniteDimensional F V]
variable (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

include hQ h2 in
/-- The actual minus eigenspace represents every field value when its dimension is at least two. -/
theorem involution_minus_represents [Finite F] (t : isometrySubgroup Q)
    (ht : Function.Involutive t.val)
    (hd : 2 ≤ Module.finrank F (minus t.val.toLinearMap)) (a : F) :
    ∃ x : minus t.val.toLinearMap, Q x.val = a := by
  have hn := minus_nondegenerate Q.polarBilin hQ t.val.toLinearMap ht
    (isometry_polar Q (isometryCarrierEquiv Q t)) h2
  have hn' : (Q.comp (minus t.val.toLinearMap).subtype).polarBilin.Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact ⟨hn.1, hn.2⟩
  exact finite_nondegenerate_represents (Q.comp (minus t.val.toLinearMap).subtype)
    hn' h2 hd a

/-- Both intrinsic invariants of any orthogonal element can be realized inside the
centralizer, using one or two reflections in the actual minus eigenspace. -/
theorem involution_centralizer_correction [Finite F] (t : isometrySubgroup Q)
    (ht : Function.Involutive t.val)
    (hd : 2 ≤ Module.finrank F (minus t.val.toLinearMap)) (g : isometrySubgroup Q) :
    ∃ c : isometrySubgroup Q, Commute t c ∧ determinant Q c = determinant Q g ∧
      spinorNorm Q hQ h2 c = spinorNorm Q hQ h2 g := by
  obtain ⟨u, hu⟩ := Atlas.squareClass_surjective F (spinorNorm Q hQ h2 g)
  obtain ⟨a, ha⟩ := involution_minus_represents Q hQ h2 t ht hd (u : F)
  obtain ⟨b, hb⟩ := involution_minus_represents Q hQ h2 t ht hd 1
  have ha0 : Q a.val ≠ 0 := ha ▸ u.ne_zero
  have hb0 : Q b.val ≠ 0 := hb ▸ one_ne_zero
  let r := reflectionElement Q a.val ha0
  let s := reflectionElement Q b.val hb0
  have hr : Commute t r := reflectionElement_commute_of_minus Q t a.val ha0
    ((mem_minus _ _).mp a.prop)
  have hs : Commute t s := reflectionElement_commute_of_minus Q t b.val hb0
    ((mem_minus _ _).mp b.prop)
  have hrs : spinorNorm Q hQ h2 r = spinorNorm Q hQ h2 g := by
    rw [spinorNorm_reflection]
    have he : Units.mk0 (Q a.val) ha0 = u := Units.ext ha
    rw [he, hu]
  have hss : spinorNorm Q hQ h2 s = 1 := by
    rw [spinorNorm_reflection]
    have he : Units.mk0 (Q b.val) hb0 = 1 := Units.ext hb
    rw [he, map_one]
  have hdet : (determinant Q g : F)^2 = 1 :=
    isometry_det_sq Q hQ (isometryCarrierEquiv Q g)
  rcases sq_eq_one_iff.mp hdet with hg | hg
  · refine ⟨r*s, hr.mul_right hs, ?_, ?_⟩
    · rw [map_mul, reflectionElement_determinant, reflectionElement_determinant]
      exact Units.ext (by simpa using hg.symm)
    · rw [map_mul, hrs, hss, mul_one]
  · refine ⟨r, hr, ?_, hrs⟩
    rw [reflectionElement_determinant]
    exact Units.ext hg.symm

end Atlas.Orthogonal
