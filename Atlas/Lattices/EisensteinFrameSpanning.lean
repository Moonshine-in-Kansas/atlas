import Atlas.Lattices.EisensteinFrameOrthogonality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra

/-- Every intrinsic frame spans the full twelve-dimensional scalar space. -/
theorem eisensteinFrameLines_span (F : EisensteinFrame) :
    (⨆ L : ↥(eisensteinFrameLines F), L.val) = ⊤ := by
  classical
  have hex (L : ↥(eisensteinFrameLines F)) :
      ∃ x : EisensteinShell 6, x ∈ eisensteinFrameVectors F ∧ eisensteinScalarLine x = L.val :=
    Finset.mem_image.mp L.property
  choose x hx hline using hex
  let v (L : ↥(eisensteinFrameLines F)) := eisensteinCoordinateEmbedding (x L).val.val
  have hv (L) : v L ∈ L.val := by
    rw [← hline L]
    exact Submodule.mem_span_singleton_self _
  have hli : LinearIndependent EisensteinRational v :=
    eisenstein_orthogonal_linearIndependent v
      (fun L => eisensteinEmbedding_ne_zero_of_norm (x L).val (by rw [(x L).property]; norm_num))
      (fun L M hne => eisensteinFrameLines_orthogonal F L.val M.val L.property M.property
        (fun h => hne (Subtype.ext h)) (v L) (hv L) (v M) (hv M))
  have hspan : Submodule.span EisensteinRational (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by
      rw [Fintype.card_coe, eisensteinFrameLines_card, eisensteinRationalCoordinates_scalar_finrank])
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨L, rfl⟩
  exact (le_iSup (fun M : ↥(eisensteinFrameLines F) => M.val) L) (hv L)

/-- Fixing every vector on every intrinsic frame line fixes the whole scalar space. -/
theorem eisensteinFrameLines_ext (F : EisensteinFrame)
    (f g : EisensteinRationalCoordinates →ₗ[EisensteinRational] EisensteinRationalCoordinates)
    (h : ∀ L ∈ eisensteinFrameLines F, ∀ v ∈ L, f v = g v) : f = g := by
  have heq : (⨆ L : ↥(eisensteinFrameLines F), L.val) ≤ LinearMap.eqLocus f g := by
    apply iSup_le
    intro L v hv
    exact h L.val L.property v hv
  rw [eisensteinFrameLines_span] at heq
  apply LinearMap.ext
  intro v
  exact heq (Submodule.mem_top)

end Atlas.Lattices
