import Atlas.GroupTheory.RankOneDoubleCoset
import Atlas.LinearGroups.Triality.UnipotentDecomposition
import Atlas.LinearGroups.Triality.WeylTorus
import Atlas.LinearGroups.Triality.ParabolicFlags

/-! Two-double-coset exhaustion of the actual parabolics. This does not yet
prove the twelve-cell decomposition or the full triality group order. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Atlas.GroupTheory
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem shortWeyl_root_twoCell (t : K) :
    TwoCell (borel F K hdeg) (shortWeyl F K) (shortWeyl F K * shortRoot F K t * shortWeyl F K) := by
  by_cases ht : t = 0
  · left
    rw [ht,shortRoot_zero,mul_one,shortWeyl_square]
    exact torus_le_borel F K hdeg ⟨_,rfl⟩
  let u : Kˣ := Units.mk0 (-t) (neg_ne_zero.mpr ht)
  have hw : shortWeyl F K * shortRoot F K t = shortNegativeRoot F K (-t) * shortWeyl F K :=
    shortWeyl_short F K t
  rw [hw,mul_assoc,shortWeyl_square,show -t = (u : K) from rfl,shortNegativeRoot_bruhat]
  right
  refine ⟨shortRoot F K (↑u⁻¹ : K) * torusMap F K (-u⁻¹,1),
    Subgroup.mul_mem _ (shortRoot_mem_borel F K hdeg _) (torus_le_borel F K hdeg ⟨_,rfl⟩),
    shortRoot F K (↑u⁻¹ : K) * torusMap F K (-1,1),
    Subgroup.mul_mem _ (shortRoot_mem_borel F K hdeg _) (torus_le_borel F K hdeg ⟨_,rfl⟩),?_⟩
  group

theorem shortWeyl_borel_twoCell (b : O_DPlus 4 K) (hb : b ∈ borel F K hdeg) :
    TwoCell (borel F K hdeg) (shortWeyl F K) (shortWeyl F K * b * shortWeyl F K) := by
  obtain ⟨r,t,h,he⟩ := borel_short_decomposition F K hdeg ⟨b,hb⟩
  change b = r.val * shortRoot F K t * torusMap F K h at he
  have hr : shortWeyl F K * r.val * (shortWeyl F K)⁻¹ ∈ borel F K hdeg := by
    apply unipotent_le_borel F K hdeg
    apply shortRadical_le_unipotent F K hdeg
    exact ((Subgroup.mem_normalizer_iff.mp (shortWeyl_normalizes_shortRadical F K hdeg)) r.val).mp r.property
  have hh : (shortWeyl F K)⁻¹ * torusMap F K h * shortWeyl F K ∈ borel F K hdeg := by
    apply torus_le_borel F K hdeg
    have hn := (Subgroup.normalizer (torus F K : Set (O_DPlus 4 K))).inv_mem
      (shortWeyl_normalizes_torus F K hdeg)
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp hn) (torusMap F K h)).mp ⟨h,rfl⟩
  have hc := twoCell_mul_right (borel F K hdeg) (shortWeyl F K)
    (twoCell_mul_left (borel F K hdeg) (shortWeyl F K) hr (shortWeyl_root_twoCell F K hdeg t)) hh
  convert hc using 1 <;> rw [he] <;> group

theorem shortParabolic_twoCell (g : O_DPlus 4 K) (hg : g ∈ shortParabolic F K hdeg) :
    g ∈ borel F K hdeg ∨ ∃ b ∈ borel F K hdeg, ∃ c ∈ borel F K hdeg, g = b * shortWeyl F K * c :=
  rankOne_double_coset_exhaustion (borel F K hdeg) (shortWeyl F K)
    (shortWeyl_borel_twoCell F K hdeg) g hg

theorem longWeyl_root_twoCell (t : F) :
    TwoCell (borel F K hdeg) (longWeyl F K) (longWeyl F K * longRoot F K t * longWeyl F K) := by
  by_cases ht : t = 0
  · left
    rw [ht,longRoot_zero,mul_one,longWeyl_square]
    exact torus_le_borel F K hdeg ⟨_,rfl⟩
  let u : Fˣ := Units.mk0 (-t) (neg_ne_zero.mpr ht)
  have hw : longWeyl F K * longRoot F K t = longNegativeRoot F K (-t) * longWeyl F K :=
    by simpa using longNegativeRoot_intertwine F K (-t)
  rw [hw,mul_assoc,longWeyl_square,show -t = (u : F) from rfl,longNegativeRoot_bruhat]
  right
  refine ⟨longRoot F K (↑u⁻¹ : F) * torusMap F K (1,-u⁻¹),
    Subgroup.mul_mem _ (longRoot_mem_borel F K hdeg _) (torus_le_borel F K hdeg ⟨_,rfl⟩),
    longRoot F K (↑u⁻¹ : F) * torusMap F K (1,-1),
    Subgroup.mul_mem _ (longRoot_mem_borel F K hdeg _) (torus_le_borel F K hdeg ⟨_,rfl⟩),?_⟩
  group

theorem longWeyl_borel_twoCell (b : O_DPlus 4 K) (hb : b ∈ borel F K hdeg) :
    TwoCell (borel F K hdeg) (longWeyl F K) (longWeyl F K * b * longWeyl F K) := by
  obtain ⟨r,t,h,he⟩ := borel_long_decomposition F K hdeg ⟨b,hb⟩
  change b = r.val * longRoot F K t * torusMap F K h at he
  have hr : longWeyl F K * r.val * (longWeyl F K)⁻¹ ∈ borel F K hdeg := by
    apply unipotent_le_borel F K hdeg
    apply longRadical_le_unipotent F K hdeg
    exact ((Subgroup.mem_normalizer_iff.mp (longWeyl_normalizes_longRadical F K hdeg)) r.val).mp r.property
  have hh : (longWeyl F K)⁻¹ * torusMap F K h * longWeyl F K ∈ borel F K hdeg := by
    apply torus_le_borel F K hdeg
    have hn := (Subgroup.normalizer (torus F K : Set (O_DPlus 4 K))).inv_mem
      (longWeyl_normalizes_torus F K hdeg)
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp hn) (torusMap F K h)).mp ⟨h,rfl⟩
  have hc := twoCell_mul_right (borel F K hdeg) (longWeyl F K)
    (twoCell_mul_left (borel F K hdeg) (longWeyl F K) hr (longWeyl_root_twoCell F K hdeg t)) hh
  convert hc using 1 <;> rw [he] <;> group

theorem longParabolic_twoCell (g : O_DPlus 4 K) (hg : g ∈ longParabolic F K hdeg) :
    g ∈ borel F K hdeg ∨ ∃ b ∈ borel F K hdeg, ∃ c ∈ borel F K hdeg, g = b * longWeyl F K * c :=
  rankOne_double_coset_exhaustion (borel F K hdeg) (longWeyl F K)
    (longWeyl_borel_twoCell F K hdeg) g hg

theorem shortWeyl_not_mem_borel : shortWeyl F K ∉ borel F K hdeg := by
  intro hn
  exact shortWeyl_not_mem_longParabolic F K hdeg
    ((le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg) hn)

theorem shortParabolic_cells_disjoint (b c : borel F K hdeg) :
    b.val * shortWeyl F K * c.val ∉ borel F K hdeg := by
  intro hg
  apply shortWeyl_not_mem_borel F K hdeg
  have hm := (borel F K hdeg).mul_mem
    ((borel F K hdeg).mul_mem ((borel F K hdeg).inv_mem b.property) hg)
    ((borel F K hdeg).inv_mem c.property)
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hm

theorem shortParabolic_mem_iff (g : O_DPlus 4 K) :
    g ∈ shortParabolic F K hdeg ↔
      g ∈ borel F K hdeg ∨ ∃ b ∈ borel F K hdeg, ∃ c ∈ borel F K hdeg, g = b * shortWeyl F K * c := by
  constructor
  · exact shortParabolic_twoCell F K hdeg g
  · rintro (hg | ⟨b,hb,c,hc,rfl⟩)
    · exact (le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) hg
    · have hn : shortWeyl F K ∈ shortParabolic F K hdeg :=
        (le_sup_right : Subgroup.closure {shortWeyl F K} ≤ _)
          (Subgroup.subset_closure (Set.mem_singleton _))
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        ((le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) hb) hn)
        ((le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) hc)

theorem longWeyl_not_mem_borel : longWeyl F K ∉ borel F K hdeg := by
  intro hn
  exact longWeyl_not_mem_shortParabolic F K hdeg
    ((le_sup_left : borel F K hdeg ≤ shortParabolic F K hdeg) hn)

theorem longParabolic_cells_disjoint (b c : borel F K hdeg) :
    b.val * longWeyl F K * c.val ∉ borel F K hdeg := by
  intro hg
  apply longWeyl_not_mem_borel F K hdeg
  have hm := (borel F K hdeg).mul_mem
    ((borel F K hdeg).mul_mem ((borel F K hdeg).inv_mem b.property) hg)
    ((borel F K hdeg).inv_mem c.property)
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hm

theorem longParabolic_mem_iff (g : O_DPlus 4 K) :
    g ∈ longParabolic F K hdeg ↔
      g ∈ borel F K hdeg ∨ ∃ b ∈ borel F K hdeg, ∃ c ∈ borel F K hdeg, g = b * longWeyl F K * c := by
  constructor
  · exact longParabolic_twoCell F K hdeg g
  · rintro (hg | ⟨b,hb,c,hc,rfl⟩)
    · exact (le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg) hg
    · have hn : longWeyl F K ∈ longParabolic F K hdeg :=
        (le_sup_right : Subgroup.closure {longWeyl F K} ≤ _)
          (Subgroup.subset_closure (Set.mem_singleton _))
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        ((le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg) hb) hn)
        ((le_sup_left : borel F K hdeg ≤ longParabolic F K hdeg) hc)

end Atlas.Triality
