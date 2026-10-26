import Atlas.LinearGroups.Type3D4

open scoped BigOperators
universe u v

theorem AtlasExistence.Triality {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 3) :
  ∃ (G : Type v) (_ : Group G), Finite G ∧
    Nat.card G = Nat.card F^12*(Nat.card F^8+Nat.card F^4+1)*
      (Nat.card F^6-1)*(Nat.card F^2-1) ∧ IsSimpleGroup G := by
  obtain ⟨G,g,hf,hs,ha,ho,_⟩ := Atlas.exists_type3D4 hdeg
  exact ⟨G,g,hf,ho,hs⟩

