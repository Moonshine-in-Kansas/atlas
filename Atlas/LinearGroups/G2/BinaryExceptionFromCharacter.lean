import Atlas.LinearGroups.G2.BinaryIndex
import Atlas.LinearGroups.G2.OrderChecks

namespace Atlas.G2.BinaryException
open Atlas.G2.Explicit

 theorem H_le_ker_of_long_root (φ : Model K →* Units ℤ)
    (hA : ∀a:K, φ (rootA a)=1) : H ≤ φ.ker := by
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨p,rfl⟩
  change φ (rootA p.toAdd.1 * rootB p.toAdd.2)=1
  rw [map_mul,hA,one_mul]
  have h := congrArg φ (weylR_rootA p.toAdd.2)
  simpa only [map_mul,map_inv,hA,mul_one,mul_inv_cancel] using h.symm

 theorem H_proper_of_character (φ : Model K →* Units ℤ)
    (hA : ∀a:K, φ (rootA a)=1) (hF : φ (rootF 1) = -1) : H ≠ ⊤ := by
  intro he
  have hh := H_le_ker_of_long_root φ hA
  have hm := hh (he ▸ Subgroup.mem_top (rootF 1))
  change φ (rootF 1)=1 at hm
  rw [hF] at hm
  norm_num at hm

 theorem index_two_of_character (φ : Model K →* Units ℤ)
    (hA : ∀a:K, φ (rootA a)=1) (hF : φ (rootF 1) = -1) : H.index=2 := by
  have hlt := H.one_lt_index_of_ne_top (H_proper_of_character φ hA hF)
  have hle := index_le_two
  omega

 theorem order_of_character (φ : Model K →* Units ℤ)
    (hA : ∀a:K, φ (rootA a)=1) (hF : φ (rootF 1) = -1) : Nat.card H=6048 := by
  have hc := H.card_mul_index
  rw [index_two_of_character φ hA hF,OrderChecks.binary_order] at hc
  omega

 theorem not_simple_of_character (φ : Model K →* Units ℤ)
    (hA : ∀a:K, φ (rootA a)=1) (hF : φ (rootF 1) = -1) : ¬ IsSimpleGroup (Model K) := by
  intro hs
  letI := hs
  rcases (inferInstance : H.Normal).eq_bot_or_eq_top with h|h
  · exact H_ne_bot h
  · exact H_proper_of_character φ hA hF h

 theorem ker_eq_H_of_character (φ : Model K →* Units ℤ)
    (hA : ∀a:K, φ (rootA a)=1) (hF : φ (rootF 1) = -1) : φ.ker=H := by
  have hproper : φ.ker ≠ ⊤ := by
    intro h
    have hf : rootF 1 ∈ φ.ker := h ▸ Subgroup.mem_top _
    change φ (rootF 1)=1 at hf
    rw [hF] at hf
    norm_num at hf
  have hi := φ.ker.one_lt_index_of_ne_top hproper
  have hc := φ.ker.card_mul_index
  rw [OrderChecks.binary_order] at hc
  have hcard : Nat.card φ.ker ≤ 6048 := by nlinarith
  symm
  apply Subgroup.eq_of_le_of_card_ge (H_le_ker_of_long_root φ hA)
  rw [order_of_character φ hA hF]
  exact hcard

end Atlas.G2.BinaryException
