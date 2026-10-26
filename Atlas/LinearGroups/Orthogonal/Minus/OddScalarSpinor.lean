import Atlas.LinearGroups.Orthogonal.Minus.PlaneReflections
import Atlas.LinearGroups.Orthogonal.SignProductD

/-! The anisotropic norm discriminant and the actual negative scalar spinor value. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.FiniteQuadratic Atlas.Quadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem trace_zero_discriminant_nonsquare (hdeg : Module.finrank F K = 2)
    (h2 : (2 : F) ≠ 0) (t : K) (ht : t ≠ 0)
    (htrace : t + conjugation F K t = 0) : ¬ IsSquare (-norm F K t) := by
  have hs : conjugation F K t = -t := eq_neg_of_add_eq_zero_right htrace
  have hsq : t^2 = algebraMap F K (-norm F K t) := by
    rw [map_neg, norm_formula hdeg, hs]
    ring
  rintro ⟨b,hb⟩
  have hb' : t^2 = (algebraMap F K b)^2 := by
    rw [hsq,hb,map_mul,pow_two]
  have hbase : ∃ b : F, algebraMap F K b = t := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hb') with h | h
    · exact ⟨b,h.symm⟩
    · exact ⟨-b,by rw [map_neg]; exact h.symm⟩
  have hfix := (conjugation_fixed_iff hdeg t).mpr hbase
  have htwo : (2 : K) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap F K).injective
    simpa only [map_ofNat,map_zero] using h
  rw [hfix] at htrace
  exact (mul_ne_zero htwo ht) (by linear_combination htrace)

/-- Actual inclusion of the split summand, acting trivially on the norm plane. -/
def splitLift (hdeg : Module.finrank F K = 2) (k : ℕ) :
    isometrySubgroup (formD k F) →* O hdeg k where
  toFun g := ⟨g.val.prodCongr (LinearEquiv.refl F K),by
    intro x
    change formD k F (g.val x.1) + norm F K x.2 = _
    rw [g.prop]
    rfl⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rfl

@[simp] theorem splitLift_apply (hdeg : Module.finrank F K = 2) (k : ℕ)
    (g : isometrySubgroup (formD k F)) (x : Vector k F K) :
    (splitLift hdeg k g).val x = (g.val x.1,x.2) := rfl

theorem splitLift_reflection (hdeg : Module.finrank F K = 2) (k : ℕ)
    (a : VectorD k F) (ha : formD k F a ≠ 0) :
    splitLift hdeg k (reflectionElement (formD k F) a ha) =
      reflectionElement (form hdeg k) (a,0) (by simpa using ha) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (reflectionLinear (formD k F) a ha x.1,x.2) =
    reflectionLinear (form hdeg k) (a,0) (by simpa using ha) x
  simp only [reflectionLinear_apply,form_apply,← normForm_apply hdeg,map_zero,
    add_zero,polar_apply,Prod.smul_mk,smul_zero]
  apply Prod.ext <;> simp

theorem splitLift_spinor (hdeg : Module.finrank F K = 2) (k : ℕ)
    (h2 : (2 : F) ≠ 0) (g : isometrySubgroup (formD k F)) :
    spinorNorm (form hdeg k) (polar_nondegenerate hdeg k) h2 (splitLift hdeg k g) =
      spinorNorm (formD k F) polarD_nondegenerate h2 g := by
  have hg : g ∈ reflectionSubgroup (formD k F) := by
    rw [reflectionSubgroup_eq_top _ polarD_nondegenerate h2]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a,ha,rfl⟩ := hg
    rw [splitLift_reflection,spinorNorm_reflection,spinorNorm_reflection]
    congr 2
    simp
  | one => simp only [map_one]
  | mul g h hg hh ihg ihh => rw [map_mul,map_mul,map_mul,ihg,ihh]
  | inv g hg ih => rw [map_inv,map_inv,map_inv,ih]

theorem splitLift_determinant (hdeg : Module.finrank F K = 2) (k : ℕ)
    (h2 : (2 : F) ≠ 0) (g : isometrySubgroup (formD k F)) :
    determinant (form hdeg k) (splitLift hdeg k g) = determinant (formD k F) g := by
  have hg : g ∈ reflectionSubgroup (formD k F) := by
    rw [reflectionSubgroup_eq_top _ polarD_nondegenerate h2]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨a,ha,rfl⟩ := hg
    rw [splitLift_reflection,reflectionElement_determinant,reflectionElement_determinant]
  | one => simp only [map_one]
  | mul g h hg hh ihg ihh => rw [map_mul,map_mul,map_mul,ihg,ihh]
  | inv g hg ih => rw [map_inv,map_inv,map_inv,ih]

/-- A tail reflection
 fixes the hyperbolic summand pointwise. -/
theorem tail_reflection_apply (hdeg : Module.finrank F K = 2) (k : ℕ)
    (a : K) (ha : normForm hdeg a ≠ 0) (x : Vector k F K) :
    (reflectionElement (form hdeg k) (0,a) (by simpa using ha)).val x =
      (x.1,(reflectionElement (normForm hdeg) a ha).val x.2) := by
  change reflectionLinear (form hdeg k) (0,a) (by simpa using ha) x =
    (x.1,reflectionLinear (normForm hdeg) a ha x.2)
  simp only [reflectionLinear_apply,form_apply,map_zero,zero_add,polar_apply,
    Prod.smul_mk,smul_zero,normForm_apply]
  apply Prod.ext <;> simp

def negativeScalar (hdeg : Module.finrank F K = 2) (k : ℕ) : O hdeg k :=
  (isometryCarrierEquiv _).symm (scalarIsometry (form hdeg k) (-1) (by ring))

theorem negativeScalar_reflection_product (hdeg : Module.finrank F K = 2) (k : ℕ)
    (t : K) (ht : t ≠ 0) (htrace : t + conjugation F K t = 0) :
    negativeScalar hdeg k = splitLift hdeg k (negativeScalarD k F) *
      reflectionElement (form hdeg k) (0,1) (by simp) *
      reflectionElement (form hdeg k) (0,t) (by simpa using
        (show normForm hdeg t ≠ 0 from fun h => ht ((normForm_eq_zero_iff hdeg t).mp h))) := by
  have hs : conjugation F K t = -t := eq_neg_of_add_eq_zero_right htrace
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (-1 : F) • x = (splitLift hdeg k (negativeScalarD k F)).val
    ((reflectionElement (form hdeg k) (0,1) (by simp)).val
      ((reflectionElement (form hdeg k) (0,t) (by simpa using (show normForm hdeg t ≠ 0 from fun h => ht ((normForm_eq_zero_iff hdeg t).mp h)))).val x))
  rw [tail_reflection_apply hdeg k t (fun h => ht ((normForm_eq_zero_iff hdeg t).mp h)),
    tail_reflection_apply hdeg k 1 (by simp),splitLift_apply]
  apply Prod.ext
  · rfl
  · change (-1 : F) • x.2 = _
    simp only [plane_reflection_apply,hs,div_neg,neg_neg,div_self ht,one_mul,
      map_one,div_one,conjugation_conjugation hdeg,neg_one_mul]
    exact neg_one_smul F x.2

theorem negativeScalar_spinorNorm (hdeg : Module.finrank F K = 2) (k : ℕ)
    (h2 : (2 : F) ≠ 0) (t : K) (ht : t ≠ 0)
    (htrace : t + conjugation F K t = 0) :
    spinorNorm (form hdeg k) (polar_nondegenerate hdeg k) h2 (negativeScalar hdeg k) =
      Atlas.squareClass F ((-1 : Fˣ)^k * Units.mk0 (norm F K t)
        (fun h => ht ((norm_zero_iff hdeg t).mp h))) := by
  rw [negativeScalar_reflection_product hdeg k t ht htrace,
    map_mul,map_mul,splitLift_spinor,negativeScalarD_spinorNorm,
    spinorNorm_reflection,spinorNorm_reflection]
  have h1 : Units.mk0 (form hdeg k (0,1)) (by simp) = (1 : Fˣ) := by
    apply Units.ext
    simp
  rw [h1,map_one,mul_one,← map_mul]
  congr 2
  apply Units.ext
  simp
theorem negativeScalar_determinant (hdeg : Module.finrank F K = 2) (k : ℕ)
    (h2 : (2 : F) ≠ 0) : determinant (form hdeg k) (negativeScalar hdeg k) = 1 := by
  obtain ⟨t,ht,htrace⟩ := exists_nonzero_trace_zero hdeg
  rw [negativeScalar_reflection_product hdeg k t ht htrace,map_mul,map_mul,
    splitLift_determinant hdeg k h2,negativeScalarD_determinant,
    reflectionElement_determinant,reflectionElement_determinant]
  simp
end Atlas.Orthogonal.Minus

