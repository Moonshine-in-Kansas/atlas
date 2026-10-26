import Mathlib.Algebra.Group.Subgroup.Ker

/-! Fixed subgroups for commuting graph and field involutions. These generic
lemmas make no existence, order, generation or simplicity assumption about a
finite group of Lie type. -/
namespace Atlas.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- Apply the field map first and the diagram map second. -/
def graphFieldTwist (graph field : G ≃* G) : G ≃* G := field.trans graph

@[simp] theorem graphFieldTwist_apply (graph field : G ≃* G) (g : G) :
    graphFieldTwist graph field g = graph (field g) := rfl

theorem graphFieldTwist_involutive (graph field : G ≃* G)
    (hg : Function.Involutive graph) (hf : Function.Involutive field)
    (hc : Function.Commute graph field) :
    Function.Involutive (graphFieldTwist graph field) := by
  intro g
  change graph (field (graph (field g))) = g
  rw [← hc (field g), hg, hf]

/-- The actual equalizer subgroup of an automorphism and the identity. -/
def automorphismFixedSubgroup (a : G ≃* G) : Subgroup G :=
  a.toMonoidHom.eqLocus (MonoidHom.id G)

@[simp] theorem mem_automorphismFixedSubgroup (a : G ≃* G) (g : G) :
    g ∈ automorphismFixedSubgroup a ↔ a g = g := Iff.rfl

theorem mem_graphFieldFixed_iff (graph field : G ≃* G)
    (hg : Function.Involutive graph) (g : G) :
    g ∈ automorphismFixedSubgroup (graphFieldTwist graph field) ↔ field g = graph g := by
  change graph (field g) = g ↔ field g = graph g
  exact hg.eq_iff

theorem fixed_pair_product (a : G ≃* G) (ha : Function.Involutive a) (g : G)
    (hc : Commute g (a g)) :
    g * a g ∈ automorphismFixedSubgroup a := by
  change a (g * a g) = g * a g
  rw [map_mul, ha]
  exact hc.eq.symm

/-- An equivariant homomorphism restricts to the actual fixed subgroups.
Surjectivity is deliberately not inferred from surjectivity on ambient groups. -/
def fixedSubgroupMap (a : G ≃* G) (b : H ≃* H) (f : G →* H)
    (hf : ∀ g, f (a g) = b (f g)) :
    automorphismFixedSubgroup a →* automorphismFixedSubgroup b where
  toFun g := ⟨f g.val, by
    have hg : a g.val = g.val := g.property
    change b (f g.val) = f g.val
    rw [← hf, hg]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' g h := Subtype.ext (map_mul f g.val h.val)

@[simp] theorem fixedSubgroupMap_val (a : G ≃* G) (b : H ≃* H) (f : G →* H)
    (hf : ∀ g, f (a g) = b (f g)) (g : automorphismFixedSubgroup a) :
    (fixedSubgroupMap a b f hf g).val = f g.val := rfl

theorem fixedSubgroupMap_injective (a : G ≃* G) (b : H ≃* H) (f : G →* H)
    (hf : ∀ g, f (a g) = b (f g)) (hinj : Function.Injective f) :
    Function.Injective (fixedSubgroupMap a b f hf) := by
  intro g h he
  apply Subtype.ext
  apply hinj
  exact congrArg Subtype.val he

end Atlas.GroupTheory
