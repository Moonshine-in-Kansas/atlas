import Atlas.LinearGroups.Triality.SignedConjugation
import Atlas.LinearGroups.Triality.RankOneGaussian
import Atlas.LinearGroups.Triality.UnipotentDecomposition
import Atlas.LinearGroups.Triality.WeylSubgroup
import Atlas.GroupTheory.FiniteCellCover

/-! Closure of the twelve actual Borel double cells under generating Weyl lifts. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal Atlas.GroupTheory
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def BruhatCellUnion (g : O_DPlus 4 K) : Prop :=
  ∃ w : Fin 12, ∃ b ∈ borel F K hdeg, ∃ c ∈ borel F K hdeg,
    g = b * weylLift F K w * c

theorem bruhat_mul_left {a g : O_DPlus 4 K} (ha : a ∈ borel F K hdeg)
    (hg : BruhatCellUnion F K hdeg g) : BruhatCellUnion F K hdeg (a*g) := by
  obtain ⟨w,b,hb,c,hc,rfl⟩ := hg
  exact ⟨w,a*b,Subgroup.mul_mem _ ha hb,c,hc,by group⟩

theorem bruhat_mul_right {a g : O_DPlus 4 K} (hg : BruhatCellUnion F K hdeg g)
    (ha : a ∈ borel F K hdeg) : BruhatCellUnion F K hdeg (g*a) := by
  obtain ⟨w,b,hb,c,hc,rfl⟩ := hg
  exact ⟨w,b,hb,c*a,Subgroup.mul_mem _ hc ha,by group⟩

theorem weylLeft_mem_bruhat (s : Bool) (w : Fin 12) :
    BruhatCellUnion F K hdeg ((if s then shortWeyl F K else longWeyl F K) * weylLift F K w) := by
  refine ⟨weylLeftIndex s w,1,Subgroup.one_mem _,
    torusMap F K (weylLeftTorus F K s w),torus_le_borel F K hdeg ⟨_,rfl⟩,?_⟩
  simpa using weylLeft_mul F K s w

theorem shortWeyl_root_bruhat (w : Fin 12) (t : K) :
    BruhatCellUnion F K hdeg (shortWeyl F K * shortRoot F K t * weylLift F K w) := by
  rcases shortWeyl_root_sign F K hdeg w with hp | hn
  · have hc := bruhat_mul_right F K hdeg (weylLeft_mem_bruhat F K hdeg true w) (hp t)
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hc
    convert hc using 1 <;> group
  · by_cases ht : t = 0
    · subst t
      simpa using weylLeft_mem_bruhat F K hdeg true w
    let a : Kˣ := Units.mk0 t ht
    rw [show t = (a : K) from rfl, shortWeyl_root_gaussian]
    have hb : shortRoot F K (↑(-a⁻¹) : K) * torusMap F K (-a⁻¹,1) ∈ borel F K hdeg :=
      Subgroup.mul_mem _ (shortRoot_mem_borel F K hdeg _) (torus_le_borel F K hdeg ⟨_,rfl⟩)
    refine ⟨w,_,hb,_,hn (↑a⁻¹ : K),?_⟩
    group

theorem shortWeyl_borel_bruhat (w : Fin 12) (b : borel F K hdeg) :
    BruhatCellUnion F K hdeg (shortWeyl F K * b.val * weylLift F K w) := by
  obtain ⟨r,t,h,he⟩ := borel_short_decomposition F K hdeg b
  have hr : shortWeyl F K * r.val * (shortWeyl F K)⁻¹ ∈ borel F K hdeg := by
    apply unipotent_le_borel F K hdeg
    apply shortRadical_le_unipotent F K hdeg
    exact ((Subgroup.mem_normalizer_iff.mp (shortWeyl_normalizes_shortRadical F K hdeg)) r.val).mp r.property
  have hh : (weylLift F K w)⁻¹ * torusMap F K h * weylLift F K w ∈ borel F K hdeg := by
    apply torus_le_borel F K hdeg
    have hn := (Subgroup.normalizer (torus F K : Set (O_DPlus 4 K))).inv_mem
      (weylLift_normalizes_torus F K hdeg w)
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp hn) (torusMap F K h)).mp ⟨h,rfl⟩
  have hc := bruhat_mul_right F K hdeg
    (bruhat_mul_left F K hdeg hr (shortWeyl_root_bruhat F K hdeg w t)) hh
  convert hc using 1 <;> rw [he] <;> group

theorem shortWeyl_bruhat_closed {g : O_DPlus 4 K} (hg : BruhatCellUnion F K hdeg g) :
    BruhatCellUnion F K hdeg (shortWeyl F K * g) := by
  obtain ⟨w,b,hb,c,hc,rfl⟩ := hg
  simpa only [mul_assoc] using bruhat_mul_right F K hdeg
    (shortWeyl_borel_bruhat F K hdeg w ⟨b,hb⟩) hc

theorem longWeyl_root_bruhat (w : Fin 12) (t : F) :
    BruhatCellUnion F K hdeg (longWeyl F K * longRoot F K t * weylLift F K w) := by
  rcases longWeyl_root_sign F K hdeg w with hp | hn
  · have hc := bruhat_mul_right F K hdeg (weylLeft_mem_bruhat F K hdeg false w) (hp t)
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hc
    convert hc using 1 <;> group
  · by_cases ht : t = 0
    · subst t
      simpa using weylLeft_mem_bruhat F K hdeg false w
    let a : Fˣ := Units.mk0 t ht
    rw [show t = (a : F) from rfl, longWeyl_root_gaussian]
    have hb : longRoot F K (↑(-a⁻¹) : F) * torusMap F K (1,-a⁻¹) ∈ borel F K hdeg :=
      Subgroup.mul_mem _ (longRoot_mem_borel F K hdeg _) (torus_le_borel F K hdeg ⟨_,rfl⟩)
    refine ⟨w,_,hb,_,hn (↑a⁻¹ : F),?_⟩
    group

theorem longWeyl_borel_bruhat (w : Fin 12) (b : borel F K hdeg) :
    BruhatCellUnion F K hdeg (longWeyl F K * b.val * weylLift F K w) := by
  obtain ⟨r,t,h,he⟩ := borel_long_decomposition F K hdeg b
  have hr : longWeyl F K * r.val * (longWeyl F K)⁻¹ ∈ borel F K hdeg := by
    apply unipotent_le_borel F K hdeg
    apply longRadical_le_unipotent F K hdeg
    exact ((Subgroup.mem_normalizer_iff.mp (longWeyl_normalizes_longRadical F K hdeg)) r.val).mp r.property
  have hh : (weylLift F K w)⁻¹ * torusMap F K h * weylLift F K w ∈ borel F K hdeg := by
    apply torus_le_borel F K hdeg
    have hn := (Subgroup.normalizer (torus F K : Set (O_DPlus 4 K))).inv_mem
      (weylLift_normalizes_torus F K hdeg w)
    simpa only [inv_inv] using ((Subgroup.mem_normalizer_iff.mp hn) (torusMap F K h)).mp ⟨h,rfl⟩
  have hc := bruhat_mul_right F K hdeg
    (bruhat_mul_left F K hdeg hr (longWeyl_root_bruhat F K hdeg w t)) hh
  convert hc using 1 <;> rw [he] <;> group

theorem longWeyl_bruhat_closed {g : O_DPlus 4 K} (hg : BruhatCellUnion F K hdeg g) :
    BruhatCellUnion F K hdeg (longWeyl F K * g) := by
  obtain ⟨w,b,hb,c,hc,rfl⟩ := hg
  simpa only [mul_assoc] using bruhat_mul_right F K hdeg
    (longWeyl_borel_bruhat F K hdeg w ⟨b,hb⟩) hc

end Atlas.Triality
