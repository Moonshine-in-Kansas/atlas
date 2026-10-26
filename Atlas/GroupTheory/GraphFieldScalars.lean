import Atlas.GroupTheory.GraphFieldFixedPoints

/-! Fixed scalar elements and transport of fixed groups. In a graph--field
twist where the graph inverts a scalar and Frobenius raises it to q, the
fixed-scalar condition is precisely the (q+1)-st root-of-unity condition.
The hypotheses on the actual graph and field actions must be proved at each
application; no center identification is assumed here. -/
namespace Atlas.GroupTheory
variable {G H : Type*} [Group G] [Group H]

theorem mem_graphFieldFixed_scalar_iff (graph field : G ≃* G)
    (hg : Function.Involutive graph) (q : ℕ) (z : G)
    (hgraph : graph z = z⁻¹) (hfield : field z = z ^ q) :
    z ∈ automorphismFixedSubgroup (graphFieldTwist graph field) ↔ z ^ (q + 1) = 1 := by
  rw [mem_graphFieldFixed_iff graph field hg, hgraph, hfield,
    eq_inv_iff_mul_eq_one, ← pow_succ]

/-- An equivariant ambient isomorphism gives an isomorphism of actual fixed
subgroups, unlike a merely surjective ambient homomorphism. -/
def fixedSubgroupEquiv (a : G ≃* G) (b : H ≃* H) (e : G ≃* H)
    (he : ∀ g, e (a g) = b (e g)) :
    automorphismFixedSubgroup a ≃* automorphismFixedSubgroup b where
  toFun := fixedSubgroupMap a b e.toMonoidHom he
  invFun h := ⟨e.symm h.val, by
    change a (e.symm h.val) = e.symm h.val
    apply e.injective
    rw [he, e.apply_symm_apply]
    exact h.property⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv h := Subtype.ext (e.apply_symm_apply h.val)
  map_mul' := (fixedSubgroupMap a b e.toMonoidHom he).map_mul

@[simp] theorem fixedSubgroupEquiv_val (a : G ≃* G) (b : H ≃* H) (e : G ≃* H)
    (he : ∀ g, e (a g) = b (e g)) (g : automorphismFixedSubgroup a) :
    (fixedSubgroupEquiv a b e he g).val = e g.val := rfl

theorem fixedSubgroupMap_mem_ker_iff (a : G ≃* G) (b : H ≃* H) (f : G →* H)
    (hf : ∀ g, f (a g) = b (f g)) (g : automorphismFixedSubgroup a) :
    g ∈ (fixedSubgroupMap a b f hf).ker ↔ g.val ∈ f.ker := by
  change fixedSubgroupMap a b f hf g = 1 ↔ f g.val = 1
  exact Subtype.ext_iff

end Atlas.GroupTheory
