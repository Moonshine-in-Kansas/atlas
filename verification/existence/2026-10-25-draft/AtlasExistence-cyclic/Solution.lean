import Atlas.Families.Cyclic.Basic

open scoped BigOperators
universe u v

theorem AtlasExistence.cyclic (p : ℕ) (hp : p.Prime) :
  ∃ (G : Type 0) (_ : Group G), Finite G ∧
    Nat.card G = p ∧ IsSimpleGroup G ∧ IsMulCommutative G := by
  refine ⟨Atlas.Families.Cyclic.Model p, inferInstance,
    Atlas.Families.Cyclic.finite p hp.pos, Atlas.Families.Cyclic.card p hp.pos,
    Atlas.Families.Cyclic.isSimpleGroup p hp, ?_⟩
  infer_instance

