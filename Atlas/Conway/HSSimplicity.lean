import Atlas.Conway.HSPrimitivity
import Atlas.GroupTheory.NormalOrderHundred

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

theorem hs_normal_factor (N : Subgroup HSModel) [N.Normal]
    [IsPretransitive N HSGraphPoints] :
    ∀ g : HSModel, ∃ n : N, ∃ k : HSMathieuModel, g = n.val*hsMathieu22Embedding k := by
  intro g
  obtain ⟨n,hn⟩ := exists_smul_eq N hsBaseGraphPoint (g • hsBaseGraphPoint)
  have hk : n.val⁻¹*g ∈ HSGraphStabilizer := by
    change (n.val⁻¹*g) • hsBaseGraphPoint = hsBaseGraphPoint
    rw [mul_smul,← hn]
    exact inv_smul_smul n.val hsBaseGraphPoint
  obtain ⟨k,hk'⟩ := hsMathieuGraphEquiv.surjective ⟨n.val⁻¹*g,hk⟩
  have he : hsMathieu22Embedding k = n.val⁻¹*g := congrArg Subtype.val hk'
  exact ⟨n,k,by rw [he,mul_inv_cancel_left]⟩

theorem hs_regular_normal_impossible (N : Subgroup HSModel) [N.Normal]
    [IsPretransitive N HSGraphPoints]
    (hf : ∀ n : N, n • hsBaseGraphPoint = hsBaseGraphPoint → n = 1) : False := by
  have hi : Function.Injective (fun n : N => n • hsBaseGraphPoint) := by
    intro u v huv
    change u • hsBaseGraphPoint = v • hsBaseGraphPoint at huv
    have hh : (u⁻¹*v) • hsBaseGraphPoint = hsBaseGraphPoint := by
      rw [mul_smul,← huv,inv_smul_smul]
    exact inv_mul_eq_one.mp (hf _ hh)
  have hc : Nat.card N = 100 := by
    rw [← hs_graph_card]
    exact Nat.card_congr (Equiv.ofBijective _ ⟨hi,fun y => exists_smul_eq N hsBaseGraphPoint y⟩)
  letI := hs_graph_primitive
  letI := hs_graph_faithful
  exact Atlas.GroupTheory.primitive_no_normal_order_hundred hsBaseGraphPoint hs_graph_card N hc

theorem hs_simple : IsSimpleGroup HSModel := by
  letI : Nontrivial HSModel := by
    obtain ⟨g,h,hne⟩ := hs_noncommuting_pair
    exact ⟨⟨g*h,h*g,hne⟩⟩
  letI := hs_graph_primitive
  letI := hs_graph_faithful
  letI := hs_graph_stabilizer_simple
  constructor
  intro N hnormal
  letI := hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  letI := Atlas.GroupTheory.normal_pretransitive (X := HSGraphPoints) N hN
  rcases (inferInstance : (N.subgroupOf HSGraphStabilizer).Normal).eq_bot_or_eq_top with hb | ht
  · exact False.elim (hs_regular_normal_impossible N (by
      intro n hn
      have hm : (⟨n.val,hn⟩ : HSGraphStabilizer) ∈ N.subgroupOf HSGraphStabilizer := n.prop
      rw [hb,Subgroup.mem_bot] at hm
      exact Subtype.ext (congrArg (fun k : HSGraphStabilizer => (k : HSModel)) hm)))
  · apply top_unique
    intro g _
    obtain ⟨n,k,hg⟩ := hs_normal_factor N g
    have hk : hsMathieu22Embedding k ∈ N := by
      have hm : hsMathieuGraphEquiv k ∈ N.subgroupOf HSGraphStabilizer := by
        rw [ht]; trivial
      exact hm
    rw [hg]
    exact N.mul_mem n.prop hk

end Atlas.Conway
