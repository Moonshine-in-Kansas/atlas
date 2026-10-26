import Atlas.Comparisons.Exceptional.E6.BinarySurjective
import Atlas.Comparisons.Exceptional.E6.IntegralDeterminant
import Atlas.LinearGroups.Orthogonal.Minus.IntrinsicEven
import Atlas.LinearGroups.Orthogonal.DicksonSiegel

/-! Integral determinant parity is the binary Dickson character. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Atlas.Orthogonal Atlas.Quadratic

def binarySign : Multiplicative (ZMod 2) →* ℤˣ where
  toFun x := (-1 : ℤˣ) ^ x.toAdd.val
  map_one' := by decide
  map_mul' := by decide

theorem binarySign_eq_one (x : Multiplicative (ZMod 2)) :
    binarySign x = 1 ↔ x = 1 := by
  revert x
  decide

theorem binary_simple_reflection_at (i : Fin 6) :
    intoBinaryOrthogonal ⟨simpleReflection ℤ i,simpleReflection_mem ℤ i⟩ =
      reflectionElement (form (ZMod 2)) (reduceBinary (simpleRoot i))
        (by rw [form_apply,norm_reduceBinary,simpleRoot_norm]; decide) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have ha := intoBinaryOrthogonal_action
    ⟨simpleReflection ℤ i,simpleReflection_mem ℤ i⟩ (binaryLift x)
  rw [reduceBinary_lift] at ha
  rw [ha]
  change reduceBinary (reflection i (binaryLift x)) =
    reflectionLinear (form (ZMod 2)) (reduceBinary (simpleRoot i))
      (by rw [form_apply,norm_reduceBinary,simpleRoot_norm]; decide) x
  rw [reflectionLinear_apply]
  simp only [form_apply,norm_reduceBinary,simpleRoot_norm,Int.cast_one,inv_one,one_mul,
    QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  have hformula : ∀ (i : Fin 6) (x : Fin 6 → ZMod 2),
      reduceBinary (reflection i (binaryLift x)) =
      x - (norm (x + reduceBinary (simpleRoot i)) - norm x -
        norm (reduceBinary (simpleRoot i))) • reduceBinary (simpleRoot i) := by
    decide
  simpa only [form_apply,norm_reduceBinary,simpleRoot_norm,Int.cast_one] using hformula i x

variable {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
variable (hdeg : Module.finrank (ZMod 2) K = 2)

def weylDickson : IntegralWeyl →* Multiplicative (ZMod 2) :=
  (Minus.fullDickson hdeg 0).comp (weylMinusEquiv hdeg).toMonoidHom

theorem weylDickson_simpleReflection (i : Fin 6) :
    weylDickson hdeg ⟨simpleReflection ℤ i,simpleReflection_mem ℤ i⟩ =
      Multiplicative.ofAdd 1 := by
  change Multiplicative.ofAdd (dicksonValue (Minus.form hdeg 2)
    (isometryGroupTransport (binaryMinusIsometry hdeg)
      (intoBinaryOrthogonal ⟨simpleReflection ℤ i,simpleReflection_mem ℤ i⟩))) = _
  rw [binary_simple_reflection_at,isometryGroupTransport_reflection,
    dicksonValue_reflection _ (Minus.polar_nondegenerate hdeg 2)]

theorem integralDeterminant_eq_binarySign (g : IntegralWeyl) :
    integralDeterminant g = binarySign (weylDickson hdeg g) := by
  let f := binarySign.comp (weylDickson hdeg)
  have hall : ∀ (a : isometrySubgroup (form ℤ)) (ha : a ∈ weyl ℤ),
      integralDeterminant ⟨a,ha⟩ = f ⟨a,ha⟩ := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨i,rfl⟩ := ha
      change integralDeterminant ⟨simpleReflection ℤ i,_⟩ =
        binarySign (weylDickson hdeg ⟨simpleReflection ℤ i,_⟩)
      rw [simpleReflection_integralDeterminant,weylDickson_simpleReflection]
      rfl
    | one => exact (map_one integralDeterminant).trans (map_one f).symm
    | mul a b ha hb ia ib =>
      change integralDeterminant (⟨a,ha⟩ * ⟨b,hb⟩) = f (⟨a,ha⟩ * ⟨b,hb⟩)
      rw [map_mul,map_mul,ia,ib]
    | inv a ha ia =>
      change integralDeterminant (⟨a,ha⟩⁻¹) = f (⟨a,ha⟩⁻¹)
      rw [map_inv,map_inv,ia]
  exact hall g.val g.prop

/-- Literal determinant-one elements are exactly the binary Dickson kernel. -/
theorem positiveWeyl_eq_dickson_kernel : positiveWeyl = (weylDickson hdeg).ker := by
  ext g
  change integralDeterminant g = 1 ↔ weylDickson hdeg g = 1
  rw [integralDeterminant_eq_binarySign hdeg,binarySign_eq_one]

/-- The retained elementary subgroup is the image of the literal positive Weyl group. -/
theorem positiveWeyl_mem_iff_elementary (g : IntegralWeyl) :
    g ∈ positiveWeyl ↔ weylMinusEquiv hdeg g ∈ Minus.E hdeg 2 := by
  rw [positiveWeyl_eq_dickson_kernel hdeg]
  rw [← Minus.fullDickson_kernel_elementary hdeg 0]
  rfl

/-- Actual positive-Weyl/elementary-minus equivalence, prior to any scalar quotient. -/
def positiveWeylMinusEquiv : positiveWeyl ≃* Minus.E hdeg 2 where
  toFun g := ⟨weylMinusEquiv hdeg g.val,(positiveWeyl_mem_iff_elementary hdeg g.val).mp g.prop⟩
  invFun g := ⟨(weylMinusEquiv hdeg).symm g.val, by
    rw [positiveWeyl_mem_iff_elementary hdeg, MulEquiv.apply_symm_apply]
    exact g.prop⟩
  left_inv g := Subtype.ext ((weylMinusEquiv hdeg).symm_apply_apply g.val)
  right_inv g := Subtype.ext ((weylMinusEquiv hdeg).apply_symm_apply g.val)
  map_mul' g h := Subtype.ext ((weylMinusEquiv hdeg).map_mul g.val h.val)

end Atlas.Comparisons.E6Lattice
