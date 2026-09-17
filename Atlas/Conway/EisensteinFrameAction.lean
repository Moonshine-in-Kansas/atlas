import Atlas.Conway.EisensteinIntegralAction
import Atlas.Lattices.EisensteinFrameVectors

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem eisensteinClassAction_one (c : EisensteinClasses) : eisensteinClassAction 1 c = c := by
  obtain ⟨z, rfl⟩ := eisensteinThetaEnd.range.mkQ_surjective c
  change eisensteinClassAction 1 (eisensteinClass z) = eisensteinClass z
  rw [eisensteinClassAction_mk, eisensteinIntegralAction_one]

theorem eisensteinClassAction_mul (g h : eisensteinHermitianGroup) (c : EisensteinClasses) :
    eisensteinClassAction (g*h) c = eisensteinClassAction g (eisensteinClassAction h c) := by
  obtain ⟨z, rfl⟩ := eisensteinThetaEnd.range.mkQ_surjective c
  change eisensteinClassAction (g*h) (eisensteinClass z) =
    eisensteinClassAction g (eisensteinClassAction h (eisensteinClass z))
  simp only [eisensteinClassAction_mk, eisensteinIntegralAction_mul]

def eisensteinShellAction (g : eisensteinHermitianGroup) (r : ℤ) :
    EisensteinShell r ≃ EisensteinShell r :=
  (eisensteinIntegralAction g).toEquiv.subtypeEquiv
    (fun z => by change eisensteinNorm z = r ↔ eisensteinNorm (eisensteinIntegralAction g z) = r
                 rw [eisensteinIntegralAction_norm])

theorem eisensteinClassAction_shell (g : eisensteinHermitianGroup) (r : ℤ)
    (c : EisensteinClasses) (hc : c ∈ eisensteinShellClasses r) :
    eisensteinClassAction g c ∈ eisensteinShellClasses r := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
  exact Finset.mem_image.mpr ⟨eisensteinShellAction g r x, Finset.mem_univ _, rfl⟩

theorem eisensteinClassAction_pair (g : eisensteinHermitianGroup) (c : EisensteinClasses) :
    (eisensteinFramePair c).image (eisensteinClassAction g) =
      eisensteinFramePair (eisensteinClassAction g c) := by
  simp [eisensteinFramePair]

/-- The actual full Hermitian group acts on intrinsic pairs of opposite short classes. -/
def eisensteinFrameAct (g : eisensteinHermitianGroup) (F : EisensteinFrame) : EisensteinFrame :=
  ⟨F.val.image (eisensteinClassAction g), by
    obtain ⟨c, hc, he⟩ := eisensteinFrame_pair F
    rw [he, eisensteinClassAction_pair]
    exact Finset.mem_image.mpr ⟨_, eisensteinClassAction_shell g 6 c hc, rfl⟩⟩

instance eisensteinFrameMulAction : MulAction eisensteinHermitianGroup EisensteinFrame where
  smul := eisensteinFrameAct
  one_smul F := by
    apply Subtype.ext
    change F.val.image (eisensteinClassAction 1) = F.val
    have he : (eisensteinClassAction 1 : EisensteinClasses → EisensteinClasses) = id :=
      funext eisensteinClassAction_one
    rw [he, Finset.image_id]
  mul_smul g h F := by
    apply Subtype.ext
    change F.val.image (eisensteinClassAction (g*h)) =
      (F.val.image (eisensteinClassAction h)).image (eisensteinClassAction g)
    rw [Finset.image_image]
    congr 1
    funext c
    exact eisensteinClassAction_mul g h c

theorem eisensteinFrameAction_vector (g : eisensteinHermitianGroup) (x : EisensteinShell 6) :
    g • eisensteinFrameOfVector x = eisensteinFrameOfVector (eisensteinShellAction g 6 x) := by
  apply Subtype.ext
  exact eisensteinClassAction_pair g (eisensteinClass x.val)

theorem eisensteinFrameAction_vectors (g : eisensteinHermitianGroup) (F : EisensteinFrame) :
    eisensteinFrameVectors (g • F) =
      (eisensteinFrameVectors F).image (eisensteinShellAction g 6) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx).2
    let y := (eisensteinShellAction g 6).symm x
    refine Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      (eisensteinShellAction g 6).apply_symm_apply x⟩
    have hy : eisensteinClassAction g (eisensteinClass y.val) = eisensteinClass x.val := by
      rw [eisensteinClassAction_mk]
      exact congrArg (fun z : EisensteinShell 6 => eisensteinClass z.val)
        ((eisensteinShellAction g 6).apply_symm_apply x)
    rwa [(eisensteinClassAction g).injective (hy.trans he.symm)]
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr
      ⟨eisensteinClass y.val, (Finset.mem_filter.mp hy).2, rfl⟩⟩

end Atlas.Conway
