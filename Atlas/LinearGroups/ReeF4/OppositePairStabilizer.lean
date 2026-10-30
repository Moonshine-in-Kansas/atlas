import Atlas.LinearGroups.ReeF4.OppositePairRecognition
import Atlas.LinearGroups.ReeF4.OppositePairScalarReduction
import Atlas.LinearGroups.ReeF4.SpecialOppositePairs

/-! Full ordered projective opposite-pair stabilizer, identified by actual
scalar normalization, induced twisted tensor recognition and six-vector rigidity.
No order theorem is used for either subgroup inclusion. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem mem_baseSpecialOppositePair_stabilizer_iff {m : ℕ} (g : Model F m) :
    g ∈ MulAction.stabilizer (Model F m) (baseSpecialOppositePair (F := F) m) ↔
      g • firstSpecialPoint (F := F) m=firstSpecialPoint m ∧
      g • oppositeSpecialPoint (F := F) m=oppositeSpecialPoint m := by
  change (g • baseSpecialOppositePair m=baseSpecialOppositePair m) ↔ _
  constructor
  · intro h
    have hh := congrArg Subtype.val h
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  · rintro ⟨he,hf⟩
    apply Subtype.ext
    exact Prod.ext he hf

theorem oppositePairStabilizer_eq_suzukiProduct {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) :
    modelSuzukiProductSubgroup hcard =
      MulAction.stabilizer (Model F m) (baseSpecialOppositePair (F := F) m) := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨⟨s,c⟩,rfl⟩
    apply (mem_baseSpecialOppositePair_stabilizer_iff _).mpr
    exact ⟨modelSuzukiProduct_fixes_first hcard s c,
      modelSuzukiProduct_fixes_opposite hcard s c⟩
  · intro hg
    obtain ⟨he,hf⟩ := (mem_baseSpecialOppositePair_stabilizer_iff g).mp hg
    obtain ⟨c,hce,hcf⟩ := model_opposite_pair_scalar_reduction hcard g he hf
    obtain ⟨s,hs⟩ := oppositeVectorStabilizer_eq_suzuki hcard
      ((modelSuzukiScalarHom hcard c)⁻¹*g) hce hcf
    refine ⟨(s,c),?_⟩
    change modelSuzukiEmbedding m hcard s * modelSuzukiScalarHom hcard c=g
    calc
      _ = modelSuzukiScalarHom hcard c * modelSuzukiEmbedding m hcard s :=
        (modelSuzuki_commutes_scalar hcard s c).eq
      _ = modelSuzukiScalarHom hcard c * ((modelSuzukiScalarHom hcard c)⁻¹*g) := by rw [hs]
      _ = g := by group

/-- The full intrinsic pair stabilizer, not just a displayed subgroup. -/
def fullOppositePairSuzukiEquiv {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) :
    Atlas.SuzukiFamily.Group F m × Fˣ ≃*
      MulAction.stabilizer (Model F m) (baseSpecialOppositePair (F := F) m) :=
  (modelSuzukiProductEquiv hcard).trans
    (MulEquiv.subgroupCongr (oppositePairStabilizer_eq_suzukiProduct hcard))

end Atlas.ReeF4
