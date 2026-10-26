import Mathlib.GroupTheory.SemidirectProduct

/-! Internal semidirect products inside a join, from normalization and disjointness.
The ambient group need not be finite and neither subgroup need be normal in it. -/

noncomputable section
namespace Atlas.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G] (H K : Subgroup G)

/-- Multiplication from the semidirect product to the actual subgroup join. -/
def normalizerJoinMulHom (hn : K ≤ Subgroup.normalizer H) :
    H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hn)] K →* ↥(H ⊔ K) :=
  (SemidirectProduct.monoidHomSubgroup hn).codRestrict (H ⊔ K)
    (fun x => Subgroup.mul_mem_sup x.left.prop x.right.prop)

theorem normalizerJoinMulHom_apply (hn : K ≤ Subgroup.normalizer H)
    (x : H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hn)] K) :
    (normalizerJoinMulHom H K hn x : G) = (x.left : G) * x.right := rfl

/-- Disjoint normalized factors give a bijection onto their actual join. -/
theorem normalizerJoinMulHom_bijective (hn : K ≤ Subgroup.normalizer H) (hd : Disjoint H K) :
    Function.Bijective (normalizerJoinMulHom H K hn) := by
  constructor
  · intro x y hxy
    have hval : (x.left : G) * x.right = (y.left : G) * y.right :=
      congrArg Subtype.val hxy
    have hp : (x.left, x.right) = (y.left, y.right) :=
      Subgroup.mul_injective_of_disjoint hd hval
    exact SemidirectProduct.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)
  · intro g
    have hg : g.val ∈ (H : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left H K hn]
      exact g.prop
    obtain ⟨u, hu, t, ht, hut⟩ := hg
    exact ⟨⟨⟨u, hu⟩, ⟨t, ht⟩⟩, Subtype.ext hut⟩

/-- The internal semidirect decomposition uses the actual conjugation action. -/
def normalizerJoinMulEquiv (hn : K ≤ Subgroup.normalizer H) (hd : Disjoint H K) :
    H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hn)] K ≃* ↥(H ⊔ K) :=
  MulEquiv.ofBijective (normalizerJoinMulHom H K hn)
    (normalizerJoinMulHom_bijective H K hn hd)

theorem normalizerJoinMulEquiv_apply (hn : K ≤ Subgroup.normalizer H) (hd : Disjoint H K)
    (x : H ⋊[(H.normalizerMonoidHom).comp (Subgroup.inclusion hn)] K) :
    (normalizerJoinMulEquiv H K hn hd x : G) = (x.left : G) * x.right := rfl

/-- Every element of the join has exactly one ordered factorization. -/
theorem normalizerJoin_existsUnique (hn : K ≤ Subgroup.normalizer H) (hd : Disjoint H K)
    (g : ↥(H ⊔ K)) : ∃! p : H × K, (p.1 : G) * p.2 = g.val := by
  obtain ⟨x, hx⟩ := (normalizerJoinMulHom_bijective H K hn hd).surjective g
  have hprod : (x.left : G) * x.right = g.val := congrArg Subtype.val hx
  refine ⟨(x.left, x.right), hprod, ?_⟩
  intro p hp
  exact Subgroup.mul_injective_of_disjoint hd (hp.trans hprod.symm)

/-- Normalization by the second factor makes the first normal inside the join. -/
theorem normalizerJoin_normal (hn : K ≤ Subgroup.normalizer H) :
    (H.subgroupOf (H ⊔ K)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le H.le_normalizer hn)

end Atlas.GroupTheory
