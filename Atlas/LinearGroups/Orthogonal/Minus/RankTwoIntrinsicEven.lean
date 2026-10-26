import Atlas.LinearGroups.Orthogonal.Minus.RankTwoComparison
import Atlas.LinearGroups.Orthogonal.Minus.FullOrder
import Atlas.LinearGroups.Orthogonal.Minus.ReflectionGeneration
import Atlas.LinearGroups.Orthogonal.DicksonEvenReflectionKernel

/-! Four-dimensional reflection generation and actual intrinsic Dickson kernel. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.Quadratic Atlas.FiniteQuadratic Matrix
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

private theorem tail_siegel_mem_even (hdeg : Module.finrank F K = 2)
    (u : Vector 1 F K) (a : K) (hu : form hdeg 1 u = 0)
    (hua : (form hdeg 1).polarBilin u (0,a) = 0) :
    siegelElement (form hdeg 1) u (0,a) hu hua ∈ evenReflectionSubgroup (form hdeg 1) := by
  by_cases ha : a = 0
  · subst a
    have he : siegelElement (form hdeg 1) u (0,0) hu hua = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      exact siegel_zero _ _ _
    rw [he]
    exact Subgroup.one_mem _
  · have hqa : form hdeg 1 (0,a) ≠ 0 := by
      simpa only [form_apply,map_zero,zero_add] using
        (show norm F K a ≠ 0 from fun h => ha ((norm_zero_iff hdeg a).mp h))
    rw [siegelElement_reflection_factor _ _ _ hu hua hqa]
    exact reflection_pair_mem_even _ _ _ _ _

theorem rankTwo_elementary_le_evenReflection (hdeg : Module.finrank F K = 2) :
    E hdeg 1 ≤ evenReflectionSubgroup (form hdeg 1) := by
  rw [← hermitianHom_range_eq_elementary hdeg]
  rintro g ⟨a,rfl⟩
  apply Atlas.sl_elementary_induction
    (fun a => hermitianHom hdeg a ∈ evenReflectionSubgroup (form hdeg 1)) _ _ a
  · intro i j hij b
    fin_cases i <;> fin_cases j <;> try contradiction
    · rw [hermitianHom_upper]
      exact tail_siegel_mem_even hdeg _ _ _ _
    · rw [hermitianHom_lower]
      exact tail_siegel_mem_even hdeg _ _ _ _
  · intro a b ha hb
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb

theorem rankTwo_reflectionSubgroup_eq_top (hdeg : Module.finrank F K = 2) :
    reflectionSubgroup (form hdeg 1) = ⊤ := by
  have h := elementary_sup_reflections_eq_top hdeg 1
  have hle := (rankTwo_elementary_le_evenReflection hdeg).trans (evenReflection_le_reflection _)
  change E hdeg 1 ⊔ reflectionSubgroup (form hdeg 1) = ⊤ at h
  rwa [sup_eq_right.mpr hle] at h

def rankTwoDickson (hdeg : Module.finrank F K = 2) :
    O hdeg 1 →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (dicksonValue (form hdeg 1) g)
  map_one' := dicksonValue_one _
  map_mul' g h := by
    apply dicksonParity_mul_of_mem_reflectionSubgroup _ (polar_nondegenerate hdeg _) g _ h
    rw [rankTwo_reflectionSubgroup_eq_top hdeg]
    trivial

theorem rankTwoDickson_surjective (hdeg : Module.finrank F K = 2) :
    Function.Surjective (rankTwoDickson hdeg) := by
  have ha : form hdeg 1 (0,1) ≠ 0 := by simp
  intro x
  obtain ⟨g,hg⟩ := reflectionDicksonCharacter_surjective (form hdeg 1)
    (polar_nondegenerate hdeg _) (0,1) ha x
  exact ⟨g.val,hg⟩

theorem rankTwoDickson_kernel_index (hdeg : Module.finrank F K = 2) :
    (rankTwoDickson hdeg).ker.index = 2 := by
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr (rankTwoDickson_surjective hdeg)]
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
  change Nat.card (ZMod 2) = 2
  simp

theorem rankTwo_elementary_le_dickson_kernel (hdeg : Module.finrank F K = 2) :
    E hdeg 1 ≤ (rankTwoDickson hdeg).ker := by
  intro g hg
  exact evenReflection_dickson_zero _ (polar_nondegenerate hdeg _)
    g (rankTwo_elementary_le_evenReflection hdeg hg)

theorem rankTwo_elementary_index_even [CharP F 2] (hdeg : Module.finrank F K = 2) :
    (E hdeg 1).index = 2 := by
  have hq : Nat.card F % 2 = 0 := by
    let := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.even_card_of_char_two (ringChar.eq F 2)
  have hp : Nat.card F ^ 2 % 2 = 0 := by rw [Nat.pow_mod,hq]
  have hpos : 1 ≤ Nat.card F ^ 2 := one_le_pow₀ Nat.card_pos
  have ho : Odd (Nat.card F^2-1) := by rw [Nat.odd_iff]; omega
  have hden : Nat.gcd 2 (Nat.card F^2-1) = 1 := ho.coprime_two_left
  have hc : Nat.card (E hdeg 1) * 2 = Nat.card (O hdeg 1) := by
    rw [rankTwo_elementary_order,hden,Nat.div_one,card_full]
    norm_num
    have hs : (Nat.card F^2+1)*(Nat.card F^2-1) = (Nat.card F^2)^2-1 := by
      nlinarith [Nat.sub_add_cancel hpos,
        Nat.sub_add_cancel (show 1 ≤ (Nat.card F^2)^2 from one_le_pow₀ (by omega))]
    rw [← hs]
    ring
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := E hdeg 1))
  exact (E hdeg 1).card_mul_index.trans hc.symm

theorem rankTwoDickson_kernel_elementary [CharP F 2] (hdeg : Module.finrank F K = 2) :
    (rankTwoDickson hdeg).ker = E hdeg 1 := by
  have he : E hdeg 1 = (rankTwoDickson hdeg).ker := by
    by_contra hne
    have hlt := Subgroup.index_strictAnti
      (lt_of_le_of_ne (rankTwo_elementary_le_dickson_kernel hdeg) hne)
    rw [rankTwo_elementary_index_even hdeg,rankTwoDickson_kernel_index hdeg] at hlt
    omega
  exact he.symm

end Atlas.Orthogonal.Minus

