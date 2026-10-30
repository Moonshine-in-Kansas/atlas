import Atlas.LinearGroups.ReeF4.OppositePairRestriction
import Atlas.LinearGroups.ReeF4.RootSuzukiIntrinsicSymplectic

/-! The actual opposite-vector restriction preserves the
symplectic form and the induced partial twisted tensor. The two same-block
lemmas are supplied by the coordinate tensor module. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem tensor_model_cross {m : ℕ} (g : Model F m) (u v : TraceZero F) :
    g.val (traceZeroCross u v)=traceZeroCross (g.val u) (g.val v) := by
  obtain ⟨hp,_⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  exact (traceZeroCross_of_forms g.val (traceZeroStabilizer_quadratic ⟨g.val,hp⟩)
    (traceZeroStabilizer_cubic ⟨g.val,hp⟩) u v).symm

private theorem tensor_model_partial {m : ℕ} (g : Model F m)
    (u v u' v' : TraceZero F) (hd : StarDomain u v) (hd' : StarDomain u' v')
    (hu : g.val u=u') (hv : g.val v=v') :
    g.val (proposedPartialProduct (thetaInv F m).toRingHom u v hd)=
      proposedPartialProduct (thetaInv F m).toRingHom u' v' hd' := by
  obtain ⟨_,hg⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  simpa only [hu,hv] using (hg u v hd).symm

private theorem tensor_scalar_root_cancel {a b : F}
    (h : a • rootVector (F := F) (0,0)=b • rootVector (0,0)) : a=b := by
  have hh := congrArg (fun w : TraceZero F => w.val.2 0 0) h
  simpa [rootVector,Pi.single_apply] using hh

variable {m : ℕ} (g : Model F m)
  (ge : g.val (rootVector (0,0))=rootVector (0,0))
  (gf : g.val (rootVector (0,7))=rootVector (0,7))

/-- Genuine form preservation on the invariant four-space. -/
theorem oppositePairLinearRestriction_polar (u v : Fin 4 → F) :
    suzukiIntrinsicPolar (oppositePairLinearRestriction g ge gf u)
      (oppositePairLinearRestriction g ge gf v)=suzukiIntrinsicPolar u v := by
  let A := oppositePairLinearRestriction g ge gf
  have hu : g.val (suzukiLeviBlockEmbed 1 u)=suzukiLeviBlockEmbed 1 (A u) :=
    (oppositePairLinearRestriction_embed g ge gf u).symm
  have hv : g.val (suzukiLeviBlockEmbed 1 v)=suzukiLeviBlockEmbed 1 (A v) :=
    (oppositePairLinearRestriction_embed g ge gf v).symm
  have hh := tensor_model_partial g _ _ _ _
    (suzukiIntrinsic_same_domain u v) (suzukiIntrinsic_same_domain (A u) (A v)) hu hv
  rw [suzukiIntrinsic_same_partial,suzukiIntrinsic_same_partial,map_smul,ge] at hh
  apply (thetaInv F m).injective
  exact (tensor_scalar_root_cancel hh).symm

/-- Cross with the fixed opposite vector propagates the restriction to block2. -/
theorem oppositePairLinearRestriction_block2 (v : Fin 4 → F) :
    g.val (suzukiLeviBlockEmbed 2 v)=
      suzukiLeviBlockEmbed 2 (oppositePairLinearRestriction g ge gf v) := by
  rw [←suzukiIntrinsic_cross_plus,tensor_model_cross,gf,
    ←oppositePairLinearRestriction_embed,suzukiIntrinsic_cross_plus]

include ge gf
/-- A−3 is forced to be fixed by the exact symplectic pairing and mixed cross
product; fixing it is not an additional stabilizer assumption. -/
theorem oppositePair_fixes_minus3 :
    g.val (rootVector (0,1))=rootVector (0,1) := by
  let u : Fin 4 → F := ![1,0,0,0]
  let v : Fin 4 → F := ![0,0,0,1]
  have hb : suzukiIntrinsicPolar u v=1 := by simp [suzukiIntrinsicPolar,u,v]
  have hh := tensor_model_cross g (suzukiLeviBlockEmbed 1 u) (suzukiLeviBlockEmbed 2 v)
  rw [suzukiIntrinsic_mixed_cross,hb,one_smul,
    ←oppositePairLinearRestriction_embed g ge gf u,
    oppositePairLinearRestriction_block2 g ge gf v,
    suzukiIntrinsic_mixed_cross,oppositePairLinearRestriction_polar,hb,one_smul] at hh
  exact hh

/-- Actual preservation of the partial inverse-Tits tensor, on its exact
symplectic-zero domain. No assertion about an oval-set stabilizer is used. -/
theorem oppositePairLinearRestriction_tensor (u v : Fin 4 → F)
    (h : suzukiIntrinsicPolar u v=0) :
    oppositePairLinearRestriction g ge gf
      (fun i => thetaInv F m (suzukiIntrinsicRawTensor u v i)) =
    fun i => thetaInv F m (suzukiIntrinsicRawTensor
      (oppositePairLinearRestriction g ge gf u)
      (oppositePairLinearRestriction g ge gf v) i) := by
  let A := oppositePairLinearRestriction g ge gf
  have hA : suzukiIntrinsicPolar (A u) (A v)=0 := by
    rw [oppositePairLinearRestriction_polar,h]
  have hp := tensor_model_partial g _ _ _ _
    (suzukiIntrinsic_mixed_domain u v h) (suzukiIntrinsic_mixed_domain (A u) (A v) hA)
    (oppositePairLinearRestriction_embed g ge gf u).symm
    (oppositePairLinearRestriction_block2 g ge gf v)
  have hh := congrArg g.val (suzukiIntrinsic_tensor_actual (thetaInv F m).toRingHom u v h)
  rw [tensor_model_cross,oppositePair_fixes_minus3 g ge gf,hp,
    suzukiIntrinsic_tensor_actual (thetaInv F m).toRingHom (A u) (A v) hA,
    ←oppositePairLinearRestriction_embed g ge gf] at hh
  exact (suzukiLeviBlockEmbed_injective 1 hh).symm
end Atlas.ReeF4
