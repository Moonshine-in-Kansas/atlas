import Mathlib.Algebra.Group.Subgroup.Basic
import Atlas.GroupTheory.PrimitiveNormal
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Simple

namespace Atlas.GroupTheory
variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPreprimitive G X]

theorem normal_sup_abelian_eq_top (a : X) (A : Subgroup G)
    (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤)
    (L : Subgroup G) [L.Normal] [MulAction.IsPretransitive L X] : L ⊔ A = ⊤ := by
  have hc : Subgroup.normalClosure (A : Set G) ≤ L ⊔ A := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨b,hb,hbx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hbx
    obtain ⟨n,hn⟩ := MulAction.exists_smul_eq L a (g • a)
    let s : MulAction.stabilizer G a := ⟨n.val⁻¹*g,by
      change (n.val⁻¹*g) • a = a
      rw [mul_smul,← hn]
      exact inv_smul_smul n.val a⟩
    let b' : MulAction.stabilizer G a := ⟨b,hA hb⟩
    have hs : s*b'*s⁻¹ ∈ A.subgroupOf (MulAction.stabilizer G a) :=
      hAn.conj_mem b' hb s
    have hsa : s.val*b*s.val⁻¹ ∈ A := hs
    have he : g*b*g⁻¹ = n.val * (s.val*b*s.val⁻¹) * n.val⁻¹ := by
      dsimp [s]
      group
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.prop)
      (Subgroup.mem_sup_right hsa)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left n.prop))
  exact top_unique (hgen ▸ hc)

theorem iwasawa_stabilizer_normal_subgroups [Group.IsPerfect G]
    (a : X) (A : Subgroup G) (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal) (hAc : IsMulCommutative A)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤)
    (L : Subgroup G) [hL : L.Normal] : L = ⊥ ∨ L = ⊤ := by
  by_cases hbot : L = ⊥
  · exact Or.inl hbot
  · letI := normal_pretransitive (X := X) L hbot
    have he := normal_sup_abelian_eq_top a A hA hAn hgen L
    have hc := hL.commutator_le_of_self_sup_commutative_eq_top he hAc
    rw [Group.IsPerfect.commutator_eq_top] at hc
    exact Or.inr (top_unique hc)

theorem iwasawa_stabilizer_simple [Nontrivial G] [Group.IsPerfect G]
    (a : X) (A : Subgroup G) (hA : A ≤ MulAction.stabilizer G a)
    (hAn : (A.subgroupOf (MulAction.stabilizer G a)).Normal) (hAc : IsMulCommutative A)
    (hgen : Subgroup.normalClosure (A : Set G) = ⊤) : IsSimpleGroup G := by
  constructor
  intro L hL
  exact iwasawa_stabilizer_normal_subgroups a A hA hAn hAc hgen L

end Atlas.GroupTheory
