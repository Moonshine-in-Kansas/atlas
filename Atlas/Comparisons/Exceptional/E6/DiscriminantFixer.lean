import Atlas.Comparisons.Exceptional.E6.Reflections
import Atlas.Comparisons.Exceptional.E6.BinaryKernel

/-! Weyl reflections fix a nonzero ternary residue of a dual-lattice vector.
This excludes the negative scalar from the binary reduction kernel. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice

def reduceTernary (x : Fin 6 → ℤ) : Fin 6 → ZMod 3 := fun i => x i

theorem linear_reduceTernary_congr
    (f : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ)) (x y : Fin 6 → ℤ)
    (h : reduceTernary x = reduceTernary y) :
    reduceTernary (f x) = reduceTernary (f y) := by
  have hd (i : Fin 6) : (3 : ℤ) ∣ y i - x i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (y i) 3).mp (congrFun h i)
  choose u hu using hd
  have he : y = x + (3 : ℤ) • u := by
    funext i
    have := hu i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    omega
  rw [he,map_add,map_smul]
  funext i
  simp only [reduceTernary,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Int.cast_add,Int.cast_mul]
  simp only [show ((3 : ℤ) : ZMod 3) = 0 by decide,zero_mul,add_zero]

def dualNumerator : Fin 6 → ℤ := ![4,5,6,4,2,3]

theorem dualNumerator_pairing :
    gram.mulVec dualNumerator = (3 : ℤ) • simpleRoot 0 := by decide

/-- Integral isometries fixing the displayed dual-lattice residue. -/
def discriminantFixer : Subgroup (Atlas.Orthogonal.isometrySubgroup (form ℤ)) where
  carrier := {g | reduceTernary (g.val dualNumerator) = reduceTernary dualNumerator}
  one_mem' := rfl
  mul_mem' {g h} hg hh :=
    (linear_reduceTernary_congr g.val.toLinearMap _ _ hh).trans hg
  inv_mem' {g} hg := by
    have h := linear_reduceTernary_congr g.val.symm.toLinearMap _ _ hg
    simpa using h.symm

theorem simpleReflection_mem_discriminantFixer (i : Fin 6) :
    simpleReflection ℤ i ∈ discriminantFixer := by
  change reduceTernary (reflection i dualNumerator) = reduceTernary dualNumerator
  revert i
  decide

theorem weyl_le_discriminantFixer : weyl ℤ ≤ discriminantFixer := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  exact simpleReflection_mem_discriminantFixer i

/-- No nonidentity element of the actual integral reflection group reduces to identity mod2. -/
theorem weyl_binary_kernel (g : weyl ℤ)
    (hred : ∀ x, reduceBinary (g.val.val x) = reduceBinary x) : g = 1 := by
  have hf : ∀ x, norm (g.val.val x) = norm x := by
    intro x
    simpa only [form_apply] using g.val.property x
  rcases binary_kernel_scalar g.val.val.toLinearMap hf hred with h | h
  · apply Subtype.ext
    apply Subtype.ext
    exact LinearEquiv.toLinearMap_injective h
  · have hg := weyl_le_discriminantFixer g.property
    change reduceTernary (g.val.val dualNumerator) = reduceTernary dualNumerator at hg
    have hn : g.val.val dualNumerator = -dualNumerator :=
      LinearMap.congr_fun h dualNumerator
    rw [hn] at hg
    have h0 := congrFun hg 0
    change (-4 : ZMod 3) = 4 at h0
    exact False.elim ((by decide : (-4 : ZMod 3) ≠ 4) h0)

end Atlas.Comparisons.E6Lattice
