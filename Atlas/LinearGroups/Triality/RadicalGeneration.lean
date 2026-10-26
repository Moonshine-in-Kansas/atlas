import Atlas.LinearGroups.Triality.ParabolicBasic

/-! The conjugates of either actual radical generate the defined group.
No perfectness, group order, parabolic maximality or simplicity is used. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

private theorem normal_intertwine {G : Type*} [_root_.Group G]
    (N : Subgroup G) [N.Normal] (w g h : G) (he : w*g=h*w) : g ∈ N ↔ h ∈ N := by
  constructor
  · intro hg
    have hc := (inferInstance : N.Normal).conj_mem g hg w
    have hh : w*g*w⁻¹ = h := by rw [he]; group
    rwa [hh] at hc
  · intro hh
    have hc := (inferInstance : N.Normal).conj_mem' h hh w
    have hg : w⁻¹*h*w = g := by
      calc
        _ = w⁻¹*(h*w) := by group
        _ = w⁻¹*(w*g) := by rw [he]
        _ = g := by group
    rwa [hg] at hc

theorem normal_eq_top_of_next_high (N : Subgroup (Group F K)) [N.Normal]
    (hn : ∀ t : K, (⟨nextShortRoot F K t, nextShortRoot_mem F K t⟩ : Group F K) ∈ N)
    (hh : ∀ b : F, (⟨highLongRoot F K b, highLongRoot_mem F K b⟩ : Group F K) ∈ N) : N = ⊤ := by
  have hs (t : K) : (⟨shortRoot F K t, shortRoot_mem F K t⟩ : Group F K) ∈ N := by
    apply (normal_intertwine N ⟨longWeyl F K, longWeyl_mem F K⟩
      ⟨shortRoot F K t, shortRoot_mem F K t⟩
      ⟨nextShortRoot F K t, nextShortRoot_mem F K t⟩
      (Subtype.ext (nextShortRoot_intertwine F K t))).mpr
    exact hn t
  have hns (t : K) : (⟨shortNegativeRoot F K t, shortNegativeRoot_mem F K t⟩ : Group F K) ∈ N := by
    apply (normal_intertwine N ⟨shortWeyl F K, shortWeyl_mem F K⟩
      ⟨shortRoot F K (-t), shortRoot_mem F K (-t)⟩
      ⟨shortNegativeRoot F K t, shortNegativeRoot_mem F K t⟩
      (Subtype.ext (by simpa using shortWeyl_short F K (-t)))).mp
    exact hs (-t)
  have hl (b : F) : (⟨longRoot F K b, longRoot_mem F K b⟩ : Group F K) ∈ N := by
    apply (normal_intertwine N ⟨shortWeyl F K, shortWeyl_mem F K⟩
      ⟨longRoot F K b, longRoot_mem F K b⟩
      ⟨highLongRoot F K (-b), highLongRoot_mem F K (-b)⟩
      (Subtype.ext (by simpa using highLongRoot_intertwine F K (-b)))).mpr
    exact hh (-b)
  have hnl (b : F) : (⟨longNegativeRoot F K b, longNegativeRoot_mem F K b⟩ : Group F K) ∈ N := by
    apply (normal_intertwine N ⟨longWeyl F K, longWeyl_mem F K⟩
      ⟨longRoot F K (-b), longRoot_mem F K (-b)⟩
      ⟨longNegativeRoot F K b, longNegativeRoot_mem F K b⟩
      (Subtype.ext (longNegativeRoot_intertwine F K b))).mp
    exact hl (-b)
  have hle : generated F K ≤ N.map (generated F K).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro g (((⟨a,rfl⟩ | ⟨a,rfl⟩) | ⟨b,rfl⟩) | ⟨b,rfl⟩)
    · exact ⟨⟨shortRoot F K a, shortRoot_mem F K a⟩, hs a, rfl⟩
    · exact ⟨⟨shortNegativeRoot F K a, shortNegativeRoot_mem F K a⟩, hns a, rfl⟩
    · exact ⟨⟨longRoot F K b, longRoot_mem F K b⟩, hl b, rfl⟩
    · exact ⟨⟨longNegativeRoot F K b, longNegativeRoot_mem F K b⟩, hnl b, rfl⟩
  apply top_unique
  intro g _
  obtain ⟨h, hh, he⟩ := hle g.property
  have heq : h = g := Subtype.ext he
  rwa [heq] at hh

theorem shortRadical_normalClosure (hdeg : Module.finrank F K = 3) :
    Subgroup.normalClosure ((shortRadical F K hdeg).subgroupOf (generated F K) : Set (Group F K)) = ⊤ := by
  apply normal_eq_top_of_next_high F K
  · intro t
    exact Subgroup.subset_normalClosure (nextShortRoot_mem_shortRadical F K hdeg t)
  · intro b
    exact Subgroup.subset_normalClosure (highLongRoot_mem_shortRadical F K hdeg b)

theorem longRadical_normalClosure (hdeg : Module.finrank F K = 3) :
    Subgroup.normalClosure ((longRadical F K hdeg).subgroupOf (generated F K) : Set (Group F K)) = ⊤ := by
  apply normal_eq_top_of_next_high F K
  · intro t
    exact Subgroup.subset_normalClosure (nextShortRoot_mem_longRadical F K hdeg t)
  · intro b
    exact Subgroup.subset_normalClosure (highLongRoot_mem_longRadical F K hdeg b)

end Atlas.Triality
