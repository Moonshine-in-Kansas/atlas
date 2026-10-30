import Atlas.LinearGroups.ReeF4.OppositePairRestriction
import Atlas.LinearGroups.ReeF4.SixVectorRigidity
import Atlas.LinearGroups.ReeF4.RootSuzukiScalarPair

/-! The four-dimensional restriction detects an actual
opposite-vector stabilizer, and a recognized Suzuki restriction lifts uniquely.
The recognition hypothesis in the last theorem remains an explicit obligation. -/
noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem negativeBlock_embed_single (i : Fin 4) :
    suzukiLeviBlockEmbed (F := F) 1 (Pi.single i 1)=
      rootVector (suzukiLeviBlockLabel 1 i) := by
  simp [suzukiLeviBlockEmbed,Pi.single_apply]

/-- The opposite vectors and the natural four-space determine the full Model
operator by the audited six-vector rigidity theorem. -/
theorem model_ext_oppositePair_block {m : ℕ} (g h : Model F m)
    (he : g.val (rootVector (0,0))=h.val (rootVector (0,0)))
    (hf : g.val (rootVector (0,7))=h.val (rootVector (0,7)))
    (hv : ∀ v : Fin 4 → F,
      g.val (suzukiLeviBlockEmbed 1 v)=h.val (suzukiLeviBlockEmbed 1 v)) : g=h := by
  have hh (i : Fin 4) :
      g.val (rootVector (suzukiLeviBlockLabel 1 i))=
        h.val (rootVector (suzukiLeviBlockLabel 1 i)) := by
    simpa only [negativeBlock_embed_single] using hv (Pi.single i 1)
  exact model_ext_six g h hf he (hh 3) (hh 2) (hh 1) (hh 0)

/-- Injectivity with explicit fixing hypotheses; no image recognition is used. -/
theorem oppositePairLinearRestriction_injective {m : ℕ} (g h : Model F m)
    (ge : g.val (rootVector (0,0))=rootVector (0,0))
    (gf : g.val (rootVector (0,7))=rootVector (0,7))
    (he : h.val (rootVector (0,0))=rootVector (0,0))
    (hf : h.val (rootVector (0,7))=rootVector (0,7))
    (hh : oppositePairLinearRestriction g ge gf = oppositePairLinearRestriction h he hf) :
    g=h := by
  apply model_ext_oppositePair_block g h (ge.trans he.symm) (gf.trans hf.symm)
  intro v
  rw [←oppositePairLinearRestriction_embed g ge gf,
    ←oppositePairLinearRestriction_embed h he hf,hh]

theorem modelSuzukiEmbedding_fixes_first {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (s : Atlas.SuzukiFamily.Group F m) :
    (modelSuzukiEmbedding m hcard s).val (rootVector (0,0))=rootVector (0,0) :=
  suzukiLeviHom_extremal_root s.val 0 (Or.inl rfl)

theorem modelSuzukiEmbedding_fixes_opposite {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (s : Atlas.SuzukiFamily.Group F m) :
    (modelSuzukiEmbedding m hcard s).val (rootVector (0,7))=rootVector (0,7) :=
  suzukiLeviHom_extremal_root s.val 7 (Or.inr rfl)

theorem modelSuzukiEmbedding_restriction_apply {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (s : Atlas.SuzukiFamily.Group F m)
    (v : Fin 4 → F) :
    oppositePairLinearRestriction (modelSuzukiEmbedding m hcard s)
      (modelSuzukiEmbedding_fixes_first hcard s)
      (modelSuzukiEmbedding_fixes_opposite hcard s) v =
        Atlas.SuzukiFamily.matrix s.val *ᵥ v := by
  have h := congrArg (fun z : SuzukiLeviCoordinates F => z.1 1)
    (suzukiLeviLinear_coordinates (Atlas.SuzukiFamily.matrix s.val)
      (suzukiLeviBlockEmbed 1 v))
  change suzukiLeviBlockProject 1
    (suzukiLeviHom s.val (suzukiLeviBlockEmbed 1 v)) =
      Atlas.SuzukiFamily.matrix s.val *ᵥ
        suzukiLeviBlockProject 1 (suzukiLeviBlockEmbed 1 v) at h
  rw [suzukiLeviBlockProject_embed] at h
  exact h

/-- If the induced four-dimensional matrix has been recognized in the actual
Suzuki group, its existing Levi embedding is the entire Model operator.
The required recognition is a substantive separate tensor calculation. -/
theorem eq_modelSuzukiEmbedding_of_restriction {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (g : Model F m)
    (ge : g.val (rootVector (0,0))=rootVector (0,0))
    (gf : g.val (rootVector (0,7))=rootVector (0,7))
    (s : Atlas.SuzukiFamily.Group F m)
    (hs : ∀ v : Fin 4 → F,
      oppositePairLinearRestriction g ge gf v=Atlas.SuzukiFamily.matrix s.val *ᵥ v) :
    g=modelSuzukiEmbedding m hcard s := by
  apply oppositePairLinearRestriction_injective g (modelSuzukiEmbedding m hcard s)
    ge gf (modelSuzukiEmbedding_fixes_first hcard s)
    (modelSuzukiEmbedding_fixes_opposite hcard s)
  apply LinearEquiv.ext
  intro v
  rw [hs,modelSuzukiEmbedding_restriction_apply]
end Atlas.ReeF4
