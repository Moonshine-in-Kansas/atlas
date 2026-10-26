import Atlas.LinearGroups.Triality.ParabolicTwoCells

/-! A single simple-root parameter suffices on the left of each nontrivial
parabolic cell. Uniqueness and cardinality are separate statements. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem borel_short_root_first (b : borel F K hdeg) :
    ∃ t : K, ∃ r : shortRadical F K hdeg, ∃ h : Kˣ × Fˣ,
      b.val = shortRoot F K t * r.val * torusMap F K h := by
  obtain ⟨r,t,h,he⟩ := borel_short_decomposition F K hdeg b
  have hx : shortRoot F K t ∈ unipotent F K hdeg := by
    rw [← shortRootInUnipotent_val F K hdeg t]
    exact (shortRootInUnipotent F K hdeg t).property
  have hn := (Subgroup.normalizer (shortRadical F K hdeg : Set (O_DPlus 4 K))).inv_mem
    (unipotent_normalizes_shortRadical F K hdeg hx)
  have hr : (shortRoot F K t)⁻¹ * r.val * shortRoot F K t ∈ shortRadical F K hdeg := by
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp hn) r.val).mp r.property
  refine ⟨t,⟨_,hr⟩,h,?_⟩
  rw [he]
  dsimp
  group

theorem shortParabolic_reduce_cell (b c : borel F K hdeg) :
    ∃ t : K, ∃ d : borel F K hdeg,
      b.val * shortWeyl F K * c.val = shortRoot F K t * shortWeyl F K * d.val := by
  obtain ⟨t,r,h,he⟩ := borel_short_root_first F K hdeg b
  have nr := (Subgroup.normalizer (shortRadical F K hdeg : Set (O_DPlus 4 K))).inv_mem
    (shortWeyl_normalizes_shortRadical F K hdeg)
  have nh := (Subgroup.normalizer (torus F K : Set (O_DPlus 4 K))).inv_mem
    (shortWeyl_normalizes_torus F K hdeg)
  have hr : (shortWeyl F K)⁻¹ * r.val * shortWeyl F K ∈ borel F K hdeg := by
    apply unipotent_le_borel F K hdeg
    apply shortRadical_le_unipotent F K hdeg
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp nr) r.val).mp r.property
  have hh : (shortWeyl F K)⁻¹ * torusMap F K h * shortWeyl F K ∈ borel F K hdeg := by
    apply torus_le_borel F K hdeg
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp nh) (torusMap F K h)).mp ⟨h,rfl⟩
  refine ⟨t,⟨_,(borel F K hdeg).mul_mem ((borel F K hdeg).mul_mem hr hh) c.property⟩,?_⟩
  rw [he]
  dsimp
  group

theorem shortParabolic_root_cell (g : O_DPlus 4 K) (hg : g ∈ shortParabolic F K hdeg) :
    g ∈ borel F K hdeg ∨ ∃ t : K, ∃ b : borel F K hdeg,
      g = shortRoot F K t * shortWeyl F K * b.val := by
  rcases shortParabolic_twoCell F K hdeg g hg with hb | ⟨b,hb,c,hc,rfl⟩
  · exact Or.inl hb
  · exact Or.inr (shortParabolic_reduce_cell F K hdeg ⟨b,hb⟩ ⟨c,hc⟩)

theorem borel_long_root_first (b : borel F K hdeg) :
    ∃ t : F, ∃ r : longRadical F K hdeg, ∃ h : Kˣ × Fˣ,
      b.val = longRoot F K t * r.val * torusMap F K h := by
  obtain ⟨r,t,h,he⟩ := borel_long_decomposition F K hdeg b
  have hx : longRoot F K t ∈ unipotent F K hdeg := by
    rw [← longRootInUnipotent_val F K hdeg t]
    exact (longRootInUnipotent F K hdeg t).property
  have hn := (Subgroup.normalizer (longRadical F K hdeg : Set (O_DPlus 4 K))).inv_mem
    (unipotent_normalizes_longRadical F K hdeg hx)
  have hr : (longRoot F K t)⁻¹ * r.val * longRoot F K t ∈ longRadical F K hdeg := by
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp hn) r.val).mp r.property
  refine ⟨t,⟨_,hr⟩,h,?_⟩
  rw [he]
  dsimp
  group

theorem longParabolic_reduce_cell (b c : borel F K hdeg) :
    ∃ t : F, ∃ d : borel F K hdeg,
      b.val * longWeyl F K * c.val = longRoot F K t * longWeyl F K * d.val := by
  obtain ⟨t,r,h,he⟩ := borel_long_root_first F K hdeg b
  have nr := (Subgroup.normalizer (longRadical F K hdeg : Set (O_DPlus 4 K))).inv_mem
    (longWeyl_normalizes_longRadical F K hdeg)
  have nh := (Subgroup.normalizer (torus F K : Set (O_DPlus 4 K))).inv_mem
    (longWeyl_normalizes_torus F K hdeg)
  have hr : (longWeyl F K)⁻¹ * r.val * longWeyl F K ∈ borel F K hdeg := by
    apply unipotent_le_borel F K hdeg
    apply longRadical_le_unipotent F K hdeg
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp nr) r.val).mp r.property
  have hh : (longWeyl F K)⁻¹ * torusMap F K h * longWeyl F K ∈ borel F K hdeg := by
    apply torus_le_borel F K hdeg
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp nh) (torusMap F K h)).mp ⟨h,rfl⟩
  refine ⟨t,⟨_,(borel F K hdeg).mul_mem ((borel F K hdeg).mul_mem hr hh) c.property⟩,?_⟩
  rw [he]
  dsimp
  group

theorem longParabolic_root_cell (g : O_DPlus 4 K) (hg : g ∈ longParabolic F K hdeg) :
    g ∈ borel F K hdeg ∨ ∃ t : F, ∃ b : borel F K hdeg,
      g = longRoot F K t * longWeyl F K * b.val := by
  rcases longParabolic_twoCell F K hdeg g hg with hb | ⟨b,hb,c,hc,rfl⟩
  · exact Or.inl hb
  · exact Or.inr (longParabolic_reduce_cell F K hdeg ⟨b,hb⟩ ⟨c,hc⟩)

end Atlas.Triality
