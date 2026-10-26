import Atlas.Rudvalis.NonorthogonalSuborbits
import Atlas.Rudvalis.ProjectiveFrameEmbedding
import Atlas.GroupTheory.OneSuborbitPrimitivity
import Mathlib.NumberTheory.Divisors

namespace Atlas.Rudvalis

/-- The exact elementary divisor obstruction for blocks in the 4060-cross action. -/
theorem rudvalis_block_arithmetic (d m : ℕ) (e : Bool)
    (h : d=1+(if e then 1755 else 0)+64*m) (hd : d∣4060) : d=1 ∨ d=4060 := by
  have ha : ∀d∈Nat.divisors 4060,d%64=1 ∨ (d%64=28 ∧ 1756≤d) → d=1 ∨ d=4060 := by decide +kernel
  apply ha d (Nat.mem_divisors.mpr ⟨hd,by decide⟩)
  cases e <;> simp only [Bool.false_eq_true,↓reduceIte] at h <;> omega

theorem rudvalis_cross_primitive : MulAction.IsPreprimitive RudvalisGroup MinimalCross := by
  let := rudvalis_cross_pretransitive
  apply Atlas.GroupTheory.primitive_of_one_suborbit_divisible_rest localReferenceCross
    (codeProjectiveHom.comp codeReferenceStabilizer.subtype)
    (fun k c=>codeGaussianHom_cross k.val c) (fun k=>k.prop)
    {c : MinimalCross | CrossOrthogonal localReferenceCross c}
    (crossOrthogonal_irrefl localReferenceCross) ?_ ?_ 64
    codeReference_nonorthogonal_orbit_divisible ?_
  · intro k c
    change CrossOrthogonal localReferenceCross (k.val • c) ↔ CrossOrthogonal localReferenceCross c
    have h := crossOrthogonal_codeGroup k.val localReferenceCross c
    rw [show k.val • localReferenceCross=localReferenceCross from k.prop] at h
    exact h
  · intro a ha b hb
    have hao : a∈MulAction.orbit localFusionGroup localThirdCross := by
      rw [localFusionGroup_orthogonal_orbit]; exact ha
    have hbo : b∈MulAction.orbit localFusionGroup localThirdCross := by
      rw [localFusionGroup_orthogonal_orbit]; exact hb
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp hao
    obtain ⟨h,hh⟩ := MulAction.mem_orbit_iff.mp hbo
    refine ⟨QuotientGroup.mk (h.val*g.val⁻¹),?_,?_⟩
    · change (h*g⁻¹) • localReferenceCross=localReferenceCross
      exact localFusionGroup_fix _
    · change (h*g⁻¹) • a=b
      rw [mul_smul,←hg,inv_smul_smul,hh]
  · intro d m e hd hdvd
    have ho : Nat.card {c : MinimalCross | CrossOrthogonal localReferenceCross c}=1755 :=
      rudvalis_orthogonal_degree _
    rw [ho] at hd
    rw [rudvalisLattice_minimal_cross_card] at hdvd ⊢
    exact rudvalis_block_arithmetic d m e hd hdvd

end Atlas.Rudvalis
