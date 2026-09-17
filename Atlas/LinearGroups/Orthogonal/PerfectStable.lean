import Atlas.LinearGroups.Orthogonal.ScalingCommutator
import Atlas.LinearGroups.Orthogonal.CompensatedTorus
import Atlas.LinearAlgebra.QuadraticComplementWitness
import Atlas.LinearGroups.Orthogonal.PerfectStandard
import Atlas.LinearGroups.Orthogonal.StandardComplement

/-! # Stable-rank intrinsic perfectness, including the ternary field -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
open scoped commutatorElement
variable {F V W : Type*} [Field F] [Finite F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W]

theorem root_mem_commutator_of_complement
    (Q : QuadraticForm F V) (H : WittTwoFrame Q)
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (e f : V) (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)
    (R : QuadraticForm F W) (g : (complementForm Q e f).IsometryEquiv R)
    (HR : WittTwoFrame R) (hR : R.polarBilin.Nondegenerate) (w : complement Q e f) :
    rootComplementHom Q e f he (Multiplicative.ofAdd w) ∈
      ⁅elementarySubgroup Q, elementarySubgroup Q⁆ := by
  obtain ⟨a, b, ha, hb, hab, hwa, hwb⟩ :=
    complement_perpendicular_pair Q R e f g HR hR h2 w
  let t := compensatedTorus Q e f he hf hef a.val b.val ha hb hab
  have ht : t ∈ elementarySubgroup Q :=
    compensatedTorus_mem_elementary Q hQ h2 e f he hf hef a.val b.val ha hb hab H
  have hte : t.val e = (-1 : F) • e := by
    rw [neg_one_smul]
    exact compensatedTorus_e Q e f he hf hef a.val b.val ha hb hab
      ((polar_swap Q e a.val).trans a.prop.1) ((polar_swap Q e b.val).trans b.prop.1)
  have htw : t.val w.val = w.val :=
    compensatedTorus_perp Q e f he hf hef a.val b.val ha hb hab w hwa hwb
  have hc : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    calc (2 : F) = 1 + 1 := by ring
         _ = -1 + 1 := by rw [h]
         _ = 0 := neg_add_cancel 1
  exact siegel_mem_commutator_of_scaling Q e w.val he
    ((polar_swap Q e w.val).trans w.prop.1) t ht (-1) hc hte htw

theorem elementary_perfect_of_standard_complements
    (Q : QuadraticForm F V) (H : WittTwoFrame Q)
    (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)
    (R : QuadraticForm F W) (HR : WittTwoFrame R) (hR : R.polarBilin.Nondegenerate)
    (hc : ∀ e f, Q e = 0 → Q f = 0 → Q.polarBilin e f = 1 →
      Nonempty ((complementForm Q e f).IsometryEquiv R)) :
    Group.IsPerfect (elementarySubgroup Q) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_left _ _) _
  apply (Subgroup.closure_le _).mpr
  rintro s ⟨u, v, hu, huv, rfl⟩
  by_cases hun : u = 0
  · subst u
    have he : siegelElement Q 0 v hu huv = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel Q 0 v x = x
      simp [siegel]
    rw [he]
    exact Subgroup.one_mem _
  · obtain ⟨f, hf, huf⟩ := exists_hyperbolic_partner Q u hu (fun h => hun (hQ.1 u h))
    obtain ⟨g⟩ := hc u f hu hf huf
    let w := rootPerpendicularRepresentative Q u f hu huf ⟨v, huv⟩
    have he := rootPerpendicularRepresentative_element Q u f hu huf ⟨v, huv⟩
    change rootComplementHom Q u f hu (Multiplicative.ofAdd w) = siegelElement Q u v hu huv at he
    rw [← he]
    exact root_mem_commutator_of_complement Q H hQ h2 u f hu hf huf R g HR hR w

theorem elementaryB_perfect_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Group.IsPerfect (elementarySubgroup (formB (n+3) F)) :=
  elementary_perfect_of_standard_complements _ (wittTwoFrameB (n+1))
    (polarB_nondegenerate h2) h2 (formB (n+2) F) (wittTwoFrameB n)
    (polarB_nondegenerate h2) (fun e f he hf hef => complement_isometryB e f he hf hef)

theorem elementaryD_perfect_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Group.IsPerfect (elementarySubgroup (formD (n+3) F)) :=
  elementary_perfect_of_standard_complements _ (wittTwoFrameD (n+1))
    polarD_nondegenerate h2 (formD (n+2) F) (wittTwoFrameD n)
    polarD_nondegenerate (fun e f he hf hef => complement_isometryD e f he hf hef)

theorem oddSpinorKernelB_perfect_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Group.IsPerfect (oddSpinorKernelB (n+3) h2) := by
  letI := elementaryB_perfect_stable n h2
  exact Group.IsPerfect.ofSurjective (f := (elementaryB_kernelEquiv (n+1) h2).toMonoidHom)
    (elementaryB_kernelEquiv (n+1) h2).surjective

theorem oddSpinorKernelD_perfect_stable (n : ℕ) (h2 : (2 : F) ≠ 0) :
    Group.IsPerfect (oddSpinorKernelD (n+3) h2) := by
  letI := elementaryD_perfect_stable n h2
  exact Group.IsPerfect.ofSurjective (f := (elementaryD_kernelEquiv (n+1) h2).toMonoidHom)
    (elementaryD_kernelEquiv (n+1) h2).surjective
end Atlas.Orthogonal
