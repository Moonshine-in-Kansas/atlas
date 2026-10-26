import Atlas.LinearGroups.Triality.RadicalRoots
import Atlas.LinearGroups.Triality.WeylRootAction
import Atlas.LinearGroups.Triality.BorelStructure

/-! Normalization of the two concrete radicals by U, H and the corresponding
simple Weyl representative, proved before any parabolic maximality assertion. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

private theorem conjugate_mem_of_intertwine {G : Type*} [_root_.Group G]
    (R : Subgroup G) {w x y : G} (h : w*x = y*w) (hy : y ∈ R) : w*x*w⁻¹ ∈ R := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]
  exact hy

theorem unipotent_normalizes_shortRadical :
    unipotent F K hdeg ≤ Subgroup.normalizer (shortRadical F K hdeg : Set (O_DPlus 4 K)) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨u, hu, rfl⟩
  let g' : unipotent F K hdeg := ⟨g, hg⟩
  refine ⟨g' * u * g'⁻¹, ?_, rfl⟩
  exact Subgroup.Normal.conj_mem inferInstance u hu g'

theorem torus_normalizes_shortRadical :
    torus F K ≤ Subgroup.normalizer (shortRadical F K hdeg : Set (O_DPlus 4 K)) := by
  rintro _ ⟨h, rfl⟩
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨p, hp, rfl⟩ := (shortRadical_mem_iff F K hdeg g).mp hg
  apply (shortRadical_mem_iff F K hdeg _).mpr
  refine ⟨torusScale F K h p, ?_, ?_⟩
  · simp [torusScale, hp]
  · rw [torus_positive_intertwine F K hdeg, mul_assoc, mul_inv_cancel, mul_one]

theorem unipotent_normalizes_longRadical :
    unipotent F K hdeg ≤ Subgroup.normalizer (longRadical F K hdeg : Set (O_DPlus 4 K)) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨u, hu, rfl⟩
  let g' : unipotent F K hdeg := ⟨g, hg⟩
  refine ⟨g' * u * g'⁻¹, ?_, rfl⟩
  exact Subgroup.Normal.conj_mem inferInstance u hu g'

theorem torus_normalizes_longRadical :
    torus F K ≤ Subgroup.normalizer (longRadical F K hdeg : Set (O_DPlus 4 K)) := by
  rintro _ ⟨h, rfl⟩
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨p, hp, rfl⟩ := (longRadical_mem_iff F K hdeg g).mp hg
  apply (longRadical_mem_iff F K hdeg _).mpr
  refine ⟨torusScale F K h p, ?_, ?_⟩
  · simp [torusScale, hp]
  · rw [torus_positive_intertwine F K hdeg, mul_assoc, mul_inv_cancel, mul_one]

theorem shortWeyl_normalizes_shortRadical :
    shortWeyl F K ∈ Subgroup.normalizer (shortRadical F K hdeg : Set (O_DPlus 4 K)) := by
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨p, hp, rfl⟩ := (shortRadical_mem_iff F K hdeg g).mp hg
  have h0 : (MulAut.conj (shortWeyl F K)) (longRoot F K p.b) ∈ shortRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (by simpa using highLongRoot_intertwine F K (-p.b))
      (highLongRoot_mem_shortRadical F K hdeg (-p.b))
  have h1 : (MulAut.conj (shortWeyl F K)) (nextShortRoot F K p.c) ∈ shortRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (shortWeyl_nextShort F K p.c)
      (middleRoot_mem_shortRadical F K hdeg (-p.c))
  have h2 : (MulAut.conj (shortWeyl F K)) (middleRoot F K p.d) ∈ shortRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (shortWeyl_middle F K p.d)
      (nextShortRoot_mem_shortRadical F K hdeg (p.d))
  have h3 : (MulAut.conj (shortWeyl F K)) (highLongRoot F K p.u) ∈ shortRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (shortWeyl_highLong F K p.u)
      (longRoot_mem_shortRadical F K hdeg (p.u))
  have h4 : (MulAut.conj (shortWeyl F K)) (highestRoot F K p.v) ∈ shortRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (shortWeyl_highest F K p.v)
      (highestRoot_mem_shortRadical F K hdeg (p.v))
  change (MulAut.conj (shortWeyl F K)) (positiveMatrix F K p) ∈ _
  simp only [positiveMatrix, positiveWord, hp, shortRoot_zero, one_mul, mul_one, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ h0 h1) h2) h3) h4
  
theorem longWeyl_normalizes_longRadical :
    longWeyl F K ∈ Subgroup.normalizer (longRadical F K hdeg : Set (O_DPlus 4 K)) := by
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨p, hp, rfl⟩ := (longRadical_mem_iff F K hdeg g).mp hg
  have h0 : (MulAut.conj (longWeyl F K)) (shortRoot F K p.a) ∈ longRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (nextShortRoot_intertwine F K p.a)
      (nextShortRoot_mem_longRadical F K hdeg (p.a))
  have h1 : (MulAut.conj (longWeyl F K)) (nextShortRoot F K p.c) ∈ longRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (longWeyl_nextShort F K p.c)
      (shortRoot_mem_longRadical F K hdeg (-p.c))
  have h2 : (MulAut.conj (longWeyl F K)) (middleRoot F K p.d) ∈ longRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (longWeyl_middle F K p.d)
      (middleRoot_mem_longRadical F K hdeg (p.d))
  have h3 : (MulAut.conj (longWeyl F K)) (highLongRoot F K p.u) ∈ longRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (highestRoot_intertwine F K p.u)
      (highestRoot_mem_longRadical F K hdeg (p.u))
  have h4 : (MulAut.conj (longWeyl F K)) (highestRoot F K p.v) ∈ longRadical F K hdeg :=
    conjugate_mem_of_intertwine _ (longWeyl_highest F K p.v)
      (highLongRoot_mem_longRadical F K hdeg (-p.v))
  change (MulAut.conj (longWeyl F K)) (positiveMatrix F K p) ∈ _
  simp only [positiveMatrix, positiveWord, hp, longRoot_zero, one_mul, mul_one, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ h0 h1) h2) h3) h4
  
end Atlas.Triality
