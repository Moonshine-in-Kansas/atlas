import Atlas.LinearGroups.ReeF4.SuzukiLeviLineFixer
import Atlas.LinearGroups.ReeF4.PointParabolicSemidirect
import Atlas.LinearGroups.ReeF4.PositiveLineKernelEmbedding

/-!
Source-only, uncompiled, including its previously staged N-coordinate prerequisites.
The new recognition route deliberately uses the independently verified actual
point-parabolic factorization. It does not use whole Ree order, whole-group
generation, simplicity, or recognition from cardinalities. The actual full
pointwise-line kernel is reduced to U before its q^11 count is transported.
An explicit root filtration and the remaining line-parabolic assembly are
separate obligations, not consequences claimed by these source drafts.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Two actual vector fixations reduce an arbitrary intrinsic Model element into U. -/
theorem model_mem_positiveRootSubgroup_of_fix_markedLine_roots {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : Model F m)
    (h0 : g.val (rootVector (F := F) (0,0)) = rootVector (0,0))
    (h2 : g.val (rootVector (F := F) (2,0)) = rootVector (2,0)) :
    g ∈ positiveRootSubgroup hcard := by
  have hp : g ∈ firstPointParabolic (F := F) m := by
    apply MulAction.mem_stabilizer_iff.mpr
    change g • specialPointMk m (rootVector (F := F) (0,0)) _ =
      specialPointMk m (rootVector (0,0)) _
    rw [specialPointMk_smul]
    apply (specialPointMk_eq_iff m _ _ _ _).mpr
    refine ⟨1, ?_⟩
    simpa only [one_smul] using h0.symm
  obtain ⟨r,l,hrl⟩ := firstPointParabolic_factorization hcard ⟨g,hp⟩
  change r.val * l.val = g at hrl
  obtain ⟨⟨s,c⟩,hl⟩ := l.property
  have hgprod : r.val * modelSuzukiProductHom hcard (s,c) = g := by
    rw [hl]
    exact hrl
  let rU : positiveRootSubgroup hcard :=
    ⟨r.val, positiveRootTailSubgroup_le_positiveRootSubgroup hcard r.property⟩
  have hc : c = 1 :=
    suzukiProduct_scalar_eq_one_of_positive_product_fix_firstRoot hcard rU s c (by
      change (r.val * modelSuzukiProductHom hcard (s,c)).val
        (rootVector (F := F) (0,0)) = rootVector (0,0)
      rw [hgprod]
      exact h0)
  subst c
  have hone : modelSuzukiProductHom hcard (s,1) = modelSuzukiEmbedding m hcard s := by
    change modelSuzukiEmbedding m hcard s * modelSuzukiScalarHom hcard 1 = _
    rw [map_one, mul_one]
  rw [hone] at hgprod
  have hsfix : (modelSuzukiEmbedding m hcard s).val
      (rootVector (F := F) (2,0)) = rootVector (2,0) :=
    modelSuzukiEmbedding_fix_second_of_positive_product_fix_second hcard rU s (by
      change (r.val * modelSuzukiEmbedding m hcard s).val
        (rootVector (F := F) (2,0)) = rootVector (2,0)
      rw [hgprod]
      exact h2)
  rw [← hgprod]
  exact (positiveRootSubgroup hcard).mul_mem rU.property
    (modelSuzukiEmbedding_mem_positiveRootSubgroup_of_fix_secondRoot hcard s hsfix)

/-- The full kernel, not only its intersection with the positive subgroup, lies in U. -/
theorem markedLineRestrictionKernel_mem_positiveRootSubgroup {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (g : markedLineRestrictionKernel (F := F) m) :
    g.val.val ∈ positiveRootSubgroup hcard := by
  have hf := (mem_markedLineRestrictionKernel_iff m g.val).mp g.property
  exact model_mem_positiveRootSubgroup_of_fix_markedLine_roots hcard g.val.val
    (hf (rootVector (0,0)) (Submodule.subset_span (by simp)))
    (hf (rootVector (2,0)) (Submodule.subset_span (by simp)))

theorem positiveLineKernelEmbedding_surjective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Surjective (positiveLineKernelEmbedding hcard) :=
  (positiveLineKernelEmbedding_surjective_iff hcard).mpr
    (markedLineRestrictionKernel_mem_positiveRootSubgroup hcard)

/-- The equivalence is the already specified inclusion, proved onto by actual reduction. -/
def positiveLineKernelEquivFull {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveLineKernel hcard ≃* markedLineRestrictionKernel (F := F) m :=
  MulEquiv.ofBijective (positiveLineKernelEmbedding hcard)
    ⟨positiveLineKernelEmbedding_injective hcard, positiveLineKernelEmbedding_surjective hcard⟩

theorem positiveLineKernelEquivFull_val {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : positiveLineKernel hcard) :
    (positiveLineKernelEquivFull hcard g).val.val = g.val.val := rfl

theorem positiveLineKernelFullParam_bijective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Function.Bijective (positiveLineKernelFullParam hcard) :=
  ⟨positiveLineKernelFullParam_injective hcard,
    (positiveLineKernelEmbedding_surjective hcard).comp (positiveLineKernelParam_surjective hcard)⟩

/-- The full pointwise kernel has the literal seven-factor, eleven-field-parameter normal form. -/
def markedLineKernelParameters {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    ((Fin 3 → F) × (Fin 4 → F × F)) ≃ markedLineRestrictionKernel (F := F) m :=
  (positiveLineKernelParameters hcard).trans (positiveLineKernelEquivFull hcard).toEquiv

theorem markedLineKernelParameters_val {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (p : (Fin 3 → F) × (Fin 4 → F × F)) :
    (markedLineKernelParameters hcard p).val.val = positiveLineKernelWord hcard p.1 p.2 := rfl

theorem card_markedLineRestrictionKernel {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Nat.card (markedLineRestrictionKernel (F := F) m) = (Nat.card F) ^ 11 := by
  rw [← Nat.card_congr (positiveLineKernelEquivFull hcard).toEquiv,
    card_positiveLineKernel hcard]

theorem markedLineRestrictionKernel_isSolvable {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Group.IsSolvable (markedLineRestrictionKernel (F := F) m) := by
  letI := positiveLineKernel_isSolvable hcard
  exact Group.isSolvable_of_isSolvable_injective
    (show Function.Injective (positiveLineKernelEquivFull hcard).symm.toMonoidHom from
      (positiveLineKernelEquivFull hcard).symm.injective)

end Atlas.ReeF4
