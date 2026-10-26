import Atlas.LinearGroups.Triality.ShortRankOne
import Atlas.LinearGroups.Triality.RootConjugation

/-! Perfectness of the actual triality matrix group, including q=2 and characteristic 3. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
open scoped commutatorElement
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem highLongRoot_mem_commutator (hdeg : Module.finrank F K = 3) (b : F) :
    (⟨highLongRoot F K b,highLongRoot_mem F K b⟩ : Group F K) ∈ commutator (Group F K) := by
  obtain ⟨t,ht⟩ := FiniteCubic.trace_surjective F K b
  subst b
  let s : Group F K := ⟨shortRoot F K 1,shortRoot_mem F K 1⟩
  let m : Group F K := ⟨middleRoot F K t,middleRoot_mem F K t⟩
  let h : Group F K := ⟨highLongRoot F K (FiniteCubic.trace F K t),highLongRoot_mem F K _⟩
  have he : s*m = h*m*s := Subtype.ext (trace_root_commutation F K hdeg t)
  have hc : ⁅s,m⁆ = h := by
    rw [commutatorElement_def,he]
    group
  change h ∈ commutator (Group F K)
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top s) (Subgroup.mem_top m)

private theorem derived_intertwine {G : Type*} [_root_.Group G] (w g h : G)
    (he : w*g = h*w) : g ∈ commutator G ↔ h ∈ commutator G := by
  constructor
  · intro hg
    have hc := (inferInstance : (commutator G).Normal).conj_mem g hg w
    have hh : w*g*w⁻¹ = h := by rw [he]; group
    rwa [hh] at hc
  · intro hh
    have hc := (inferInstance : (commutator G).Normal).conj_mem' h hh w
    have hg : w⁻¹*h*w = g := by
      calc
        _ = w⁻¹*(h*w) := by group
        _ = w⁻¹*(w*g) := by rw [he]
        _ = g := by group
    rwa [hg] at hc

theorem longRoot_mem_commutator (hdeg : Module.finrank F K = 3) (b : F) :
    (⟨longRoot F K b,longRoot_mem F K b⟩ : Group F K) ∈ commutator (Group F K) := by
  let w : Group F K := ⟨shortWeyl F K,shortWeyl_mem F K⟩
  let g : Group F K := ⟨longRoot F K b,longRoot_mem F K b⟩
  let h : Group F K := ⟨highLongRoot F K (-b),highLongRoot_mem F K (-b)⟩
  have he : w*g=h*w := by
    apply Subtype.ext
    change shortWeyl F K * longRoot F K b = highLongRoot F K (-b) * shortWeyl F K
    simpa only [neg_neg] using highLongRoot_intertwine F K (-b)
  exact (derived_intertwine w g h he).mpr (highLongRoot_mem_commutator F K hdeg (-b))

theorem longNegativeRoot_mem_commutator (hdeg : Module.finrank F K = 3) (b : F) :
    (⟨longNegativeRoot F K b,longNegativeRoot_mem F K b⟩ : Group F K) ∈ commutator (Group F K) := by
  let w : Group F K := ⟨longWeyl F K,longWeyl_mem F K⟩
  let g : Group F K := ⟨longRoot F K (-b),longRoot_mem F K (-b)⟩
  let h : Group F K := ⟨longNegativeRoot F K b,longNegativeRoot_mem F K b⟩
  have he : w*g=h*w := Subtype.ext (longNegativeRoot_intertwine F K b)
  exact (derived_intertwine w g h he).mp (longRoot_mem_commutator F K hdeg (-b))

theorem perfect (hdeg : Module.finrank F K = 3) : _root_.Group.IsPerfect (Group F K) := by
  have hle : generated F K ≤ (commutator (Group F K)).map (generated F K).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro g (((⟨a,rfl⟩ | ⟨a,rfl⟩) | ⟨b,rfl⟩) | ⟨b,rfl⟩)
    · exact ⟨⟨shortRoot F K a,shortRoot_mem F K a⟩,shortRoot_mem_commutator F K hdeg a,rfl⟩
    · exact ⟨⟨shortNegativeRoot F K a,shortNegativeRoot_mem F K a⟩,
        shortNegativeRoot_mem_commutator F K hdeg a,rfl⟩
    · exact ⟨⟨longRoot F K b,longRoot_mem F K b⟩,longRoot_mem_commutator F K hdeg b,rfl⟩
    · exact ⟨⟨longNegativeRoot F K b,longNegativeRoot_mem F K b⟩,
        longNegativeRoot_mem_commutator F K hdeg b,rfl⟩
  constructor
  apply top_unique
  intro g _
  obtain ⟨h,hh,he⟩ := hle g.property
  have heq : h=g := Subtype.ext he
  rwa [heq] at hh

theorem noncommutative (hdeg : Module.finrank F K = 3) : ¬ IsMulCommutative (Group F K) := by
  letI := perfect F K hdeg
  exact _root_.Group.IsPerfect.not_isMulCommutative (Group F K)

end Atlas.Triality
