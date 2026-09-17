import Atlas.Algebra.EisensteinApproximation
import Atlas.Lattices.EisensteinClassBounds

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators QuadraticAlgebra

/-- The field norm is the positive scalar norm in the complex embedding. -/
theorem eisensteinRational_norm_eq_real (c : EisensteinRational) :
    c.norm = eisensteinReal (star c * c) := by
  rw [QuadraticAlgebra.norm_def, eisensteinReal_star_mul_self]
  ring

theorem eisensteinToRational_norm (a : Eisenstein) :
    (eisensteinToRational a).norm = (a.norm : ℚ) := by
  simp [QuadraticAlgebra.norm_def, eisensteinToRational]

theorem eisensteinBilinear_self_sum_norm (z : EisensteinRationalCoordinates) :
    eisensteinBilinear z z = (2/9 : ℚ) * ∑ i, (z i).norm := by
  rw [eisensteinBilinear_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [QuadraticAlgebra.norm_def]
  ring

/-- Multiplication by a rational Eisenstein scalar scales squared length by its field norm. -/
theorem eisensteinBilinear_scalar_self (c : EisensteinRational)
    (z : EisensteinRationalCoordinates) :
    eisensteinBilinear (c • z) (c • z) = c.norm * eisensteinBilinear z z := by
  rw [eisensteinBilinear_self_sum_norm, eisensteinBilinear_self_sum_norm]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum]
  ring

theorem eisensteinCoordinateEmbedding_smul (a : Eisenstein) (z : EisensteinCoordinates) :
    eisensteinCoordinateEmbedding (a • z) =
      eisensteinToRational a • eisensteinCoordinateEmbedding z := by
  funext i
  exact map_mul eisensteinToRational a (z i)

theorem eisensteinNorm_smul (a : Eisenstein) (x : EisensteinLattice) :
    eisensteinNorm (a • x) = (a.norm : ℚ) * eisensteinNorm x := by
  unfold eisensteinNorm
  rw [Submodule.coe_smul, eisensteinCoordinateEmbedding_smul,
    eisensteinBilinear_scalar_self, eisensteinToRational_norm]

theorem eisensteinEmbedding_ne_zero_of_norm
    (x : EisensteinLattice) (hx : eisensteinNorm x ≠ 0) : eisensteinCoordinateEmbedding x.val ≠ 0 := by
  intro h
  apply hx
  unfold eisensteinNorm
  rw [h]
  simp [eisensteinBilinear, eisensteinHermitian, eisensteinReal]

/-- A scalar taking one norm-six lattice vector to another is an integral
Eisenstein unit. The residual after nearest-lattice approximation has norm at
most three, so the actual Leech minimum four forces it to vanish. -/
theorem eisenstein_six_scalar_integral_unit
    (x y : EisensteinLattice) (hx : eisensteinNorm x = 6) (hy : eisensteinNorm y = 6)
    (c : EisensteinRational)
    (hc : eisensteinCoordinateEmbedding y.val = c • eisensteinCoordinateEmbedding x.val) :
    ∃ a : Eisenstein, c = eisensteinToRational a ∧ a.norm = 1 ∧ y = a • x := by
  obtain ⟨a, ha⟩ := eisenstein_rational_approximation c
  let z : EisensteinLattice := y - a • x
  have hz : eisensteinCoordinateEmbedding z.val =
      (c-eisensteinToRational a) • eisensteinCoordinateEmbedding x.val := by
    change eisensteinCoordinateEmbedding (y.val - a • x.val) = _
    rw [map_sub, eisensteinCoordinateEmbedding_smul, hc, sub_smul]
  have hzn : eisensteinNorm z = (c-eisensteinToRational a).norm * 6 := by
    unfold eisensteinNorm
    rw [hz, eisensteinBilinear_scalar_self]
    change _ = _
    rw [show eisensteinBilinear (eisensteinCoordinateEmbedding x.val)
      (eisensteinCoordinateEmbedding x.val) = 6 from hx]
  have hz0 : z = 0 := by
    by_contra hn
    have hm := eisensteinNorm_minimum z hn
    rw [hzn] at hm
    nlinarith [ha]
  have hyx : y = a • x := sub_eq_zero.mp hz0
  have hnx : eisensteinCoordinateEmbedding x.val ≠ 0 :=
    eisensteinEmbedding_ne_zero_of_norm x (by rw [hx]; norm_num)
  have hscalar : c = eisensteinToRational a := by
    rw [hz0, Submodule.coe_zero, map_zero] at hz
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz.symm).resolve_right hnx)
  have hna : a.norm = 1 := by
    have hh := eisensteinNorm_smul a x
    rw [← hyx, hx, hy] at hh
    have hq : (a.norm : ℚ) = 1 := by linarith
    exact_mod_cast hq
  exact ⟨a, hscalar, hna, hyx⟩

/-- Same scalar line for norm-six lattice vectors means multiplication by an
actual integral unit; the unit group has the already verified six elements. -/
theorem eisenstein_six_sameLine_unit
    (x y : EisensteinLattice) (hx : eisensteinNorm x = 6) (hy : eisensteinNorm y = 6)
    (hc : ∃ c : EisensteinRational,
      eisensteinCoordinateEmbedding y.val = c • eisensteinCoordinateEmbedding x.val) :
    ∃ u : Eisensteinˣ, y = (u : Eisenstein) • x := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨a, ha, hn, hyx⟩ := eisenstein_six_scalar_integral_unit x y hx hy c hc
  obtain ⟨u, hu⟩ := (eisenstein_isUnit_iff a).mpr hn
  exact ⟨u, hu ▸ hyx⟩

/-- Norm-six vectors on the actual scalar line through a fixed norm-six vector. -/
def EisensteinSixLineFiber (x : EisensteinShell 6) :=
  {y : EisensteinShell 6 // ∃ c : EisensteinRational,
    eisensteinCoordinateEmbedding y.val.val = c • eisensteinCoordinateEmbedding x.val.val}

def eisensteinSixLineUnitMap (x : EisensteinShell 6) : Eisensteinˣ → EisensteinSixLineFiber x :=
  fun u => ⟨⟨(u : Eisenstein) • x.val, by
    have hu := (eisenstein_isUnit_iff (u : Eisenstein)).mp u.isUnit
    rw [eisensteinNorm_smul, hu, x.property]
    norm_num⟩,
    ⟨eisensteinToRational (u : Eisenstein), eisensteinCoordinateEmbedding_smul _ _⟩⟩

theorem eisensteinSixLineUnitMap_bijective (x : EisensteinShell 6) :
    Function.Bijective (eisensteinSixLineUnitMap x) := by
  constructor
  · intro u v h
    apply Units.ext
    apply eisensteinToRational_injective
    have he := congrArg (fun y : EisensteinSixLineFiber x =>
      eisensteinCoordinateEmbedding y.val.val.val) h
    change eisensteinCoordinateEmbedding ((u : Eisenstein) • x.val.val) =
      eisensteinCoordinateEmbedding ((v : Eisenstein) • x.val.val) at he
    rw [eisensteinCoordinateEmbedding_smul, eisensteinCoordinateEmbedding_smul] at he
    have hz : (eisensteinToRational (u : Eisenstein) - eisensteinToRational (v : Eisenstein)) •
        eisensteinCoordinateEmbedding x.val.val = 0 := by
      rw [sub_smul, he, sub_self]
    have hx := eisensteinEmbedding_ne_zero_of_norm x.val (by rw [x.property]; norm_num)
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hx)
  · intro y
    obtain ⟨u, hu⟩ := eisenstein_six_sameLine_unit x.val y.val.val x.property y.val.property y.property
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu.symm

/-- Explicit unit parametrization of every norm-six scalar line. -/
def eisensteinSixLineUnitsEquiv (x : EisensteinShell 6) :
    Eisensteinˣ ≃ EisensteinSixLineFiber x :=
  Equiv.ofBijective (eisensteinSixLineUnitMap x) (eisensteinSixLineUnitMap_bijective x)

/-- Every scalar line meeting the norm-six shell contains exactly six such vectors. -/
theorem eisenstein_six_line_card (x : EisensteinShell 6) :
    Nat.card (EisensteinSixLineFiber x) = 6 := by
  rw [← Nat.card_congr (eisensteinSixLineUnitsEquiv x)]
  exact eisenstein_units_card

end Atlas.Lattices
