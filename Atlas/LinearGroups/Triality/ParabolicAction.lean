import Atlas.LinearGroups.Triality.TorusCore
import Atlas.LinearGroups.Triality.ParabolicMaximal
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Quotient

/-! The actual faithful primitive parabolic coset action of the matrix group. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

def parabolic : Subgroup (Group F K) := (longParabolic F K hdeg).subgroupOf (generated F K)
abbrev ParabolicPoints := Group F K ⧸ parabolic F K hdeg

theorem parabolic_ne_top : parabolic F K hdeg ≠ ⊤ := by
  intro he
  have hh : (⟨shortWeyl F K,shortWeyl_mem F K⟩ : Group F K) ∈ parabolic F K hdeg :=
    he ▸ Subgroup.mem_top _
  exact shortWeyl_not_mem_longParabolic F K hdeg hh

theorem parabolic_isCoatom : IsCoatom (parabolic F K hdeg) := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨parabolic_ne_top F K hdeg,?_⟩
  intro H htop hPH
  let f := (generated F K).subtype
  have hP : longParabolic F K hdeg ≤ H.map f := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (longParabolic_le_generated F K hdeg)]
    exact Subgroup.map_mono hPH
  have hG : H.map f ≤ generated F K := by
    rintro _ ⟨g,hg,rfl⟩
    exact g.property
  rcases longParabolic_overgroup F K hdeg (H.map f) hP hG with hp|hg
  · intro g h
    have hh : g.val ∈ H.map f := ⟨g,h,rfl⟩
    rw [hp] at hh
    exact hh
  · apply False.elim
    apply htop
    apply top_unique
    intro g _
    have hh : g.val ∈ H.map f := by rw [hg]; exact g.property
    obtain ⟨x,hx,he⟩ := hh
    have he' : x=g := Subtype.ext he
    exact he' ▸ hx

theorem parabolic_normalCore_eq_bot : (parabolic F K hdeg).normalCore=⊥ := by
  let N := (parabolic F K hdeg).normalCore
  let f := (generated F K).subtype
  have hP : N.map f ≤ longParabolic F K hdeg := by
    rintro _ ⟨g,hg,rfl⟩
    exact (parabolic F K hdeg).normalCore_le hg
  have hc : ∀ a ∈ generated F K, ∀ g ∈ N.map f, a*g*a⁻¹ ∈ N.map f := by
    rintro a ha g ⟨x,hx,rfl⟩
    let b : Group F K := ⟨a,ha⟩
    exact ⟨b*x*b⁻¹,Subgroup.Normal.conj_mem inferInstance x hx b,rfl⟩
  have hn := normal_in_longParabolic_eq_bot F K hdeg (N.map f) hP hc
  apply le_antisymm _ bot_le
  intro g hg
  have hh : g.val ∈ N.map f := ⟨g,hg,rfl⟩
  rw [hn] at hh
  exact Subtype.ext hh

instance parabolicPoints_nontrivial : Nontrivial (ParabolicPoints F K hdeg) := by
  let g : Group F K := ⟨shortWeyl F K,shortWeyl_mem F K⟩
  refine ⟨⟨(g : ParabolicPoints F K hdeg),((1 : Group F K) : ParabolicPoints F K hdeg),?_⟩⟩
  intro he
  have hh := QuotientGroup.eq.mp he
  have hg : g ∈ parabolic F K hdeg := by
    apply (parabolic F K hdeg).inv_mem_iff.mp
    simpa using hh
  exact shortWeyl_not_mem_longParabolic F K hdeg hg

instance parabolicPoints_faithful : FaithfulSMul (Group F K) (ParabolicPoints F K hdeg) := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hh : g ∈ (MulAction.toPermHom (Group F K) (ParabolicPoints F K hdeg)).ker := by
    apply Equiv.Perm.ext
    exact hg
  rw [← Subgroup.normalCore_eq_ker,parabolic_normalCore_eq_bot F K hdeg] at hh
  exact hh

instance parabolicPoints_primitive : MulAction.IsPreprimitive (Group F K) (ParabolicPoints F K hdeg) := by
  apply (MulAction.isCoatom_stabilizer_iff_preprimitive (Group F K)
    ((1 : Group F K) : ParabolicPoints F K hdeg)).mp
  rw [MulAction.stabilizer_quotient]
  exact parabolic_isCoatom F K hdeg

end Atlas.Triality
