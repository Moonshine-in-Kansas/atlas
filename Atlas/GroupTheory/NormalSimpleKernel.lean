import Atlas.GroupTheory.NormalSimpleImage
import Mathlib.GroupTheory.Commutator.Basic

namespace Atlas.GroupTheory
open scoped commutatorElement

/-- A noncentral element in a normal subgroup forces it to contain a simple kernel. -/
theorem simple_kernel_le_normal_of_noncommuting {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) [IsSimpleGroup f.ker] (N : Subgroup G) [N.Normal]
    (s : G) (hs : s ∈ N) (k : f.ker) (hn : s*k.val ≠ k.val*s) : f.ker ≤ N := by
  let c : f.ker := ⟨⁅s,k.val⁆,by
    change f (s*k.val*s⁻¹*k.val⁻¹) = 1
    simp only [map_mul,map_inv,show f k.val = 1 from k.prop,mul_one,inv_one,
      mul_inv_cancel]⟩
  have hcN : c.val ∈ N := by
    change (s*k.val*s⁻¹*k.val⁻¹) ∈ N
    have hh := (inferInstance : N.Normal).conj_mem s⁻¹ (N.inv_mem hs) k.val
    have h := N.mul_mem hs hh
    change s * (k.val * s⁻¹ * k.val⁻¹) ∈ N at h
    simpa only [mul_assoc] using h
  have hcn : c ≠ 1 := by
    intro he
    have h : ⁅s,k.val⁆ = 1 := congrArg Subtype.val he
    exact hn (commutatorElement_eq_one_iff_mul_comm.mp h)
  have ht : N.comap f.ker.subtype = ⊤ := by
    rcases (inferInstance : (N.comap f.ker.subtype).Normal).eq_bot_or_eq_top with hb | ht
    · have h : c ∈ N.comap f.ker.subtype := hcN
      rw [hb] at h
      exact (hcn h).elim
    · exact ht
  intro x hx
  have h : (⟨x,hx⟩ : f.ker) ∈ N.comap f.ker.subtype := ht ▸ Subgroup.mem_top _
  exact h

end Atlas.GroupTheory
