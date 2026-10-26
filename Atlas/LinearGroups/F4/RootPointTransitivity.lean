import Atlas.LinearGroups.F4.RootPointMove
import Atlas.LinearGroups.F4.RadicalRegular
import Atlas.LinearGroups.F4.RadicalDerived

/-! Projective transitivity of the actual root-generated subgroup, without
using torus generation, full-stabilizer fullness, or the target group order. -/
noncomputable section
set_option maxRecDepth 4096
namespace Atlas.F4
open Atlas.Albert
open scoped LinearAlgebra.Projectivization
variable {F : Type*} [Field F]

theorem whiteZero_from_base_generated (x : Carrier F) (hx : x≠0)
    (ha : adjoint x=0) (ht : trace x=0) :
    ∃g : Model F, g∈rootGenerated ∧ ∃s : Fˣ,
      g.val (oppositeBaseCell (F:=F)).val=s.val • x := by
  obtain ⟨k,hk,hc⟩ := whiteZero_move_to_open_generated x hx ha ht
  let s : Fˣ := (Units.mk0 ((k.val x).2 2 7) hc)⁻¹
  let y : OppositeCell F := ⟨s.val • k.val x,by
    refine ⟨?_,?_,?_⟩
    · rw [adjoint_smul,stabilizer_adjoint,ha,map_zero,smul_zero]
    · change parabolicTrace (s.val • k.val x)=0
      rw [map_smul]
      change s.val*trace (k.val x)=0
      rw [stabilizer_trace,ht,mul_zero]
    · change ((k.val x).2 2 7)⁻¹*(k.val x).2 2 7=1
      exact inv_mul_cancel₀ hc⟩
  let p := radicalBetween (oppositeBaseCell (F:=F)) y
  have hp : (radicalElement p).val (oppositeBaseCell (F:=F)).val=y.val := by
    have h := congrArg Subtype.val (radicalBetween_apply (oppositeBaseCell (F:=F)) y)
    rw [radicalOpposite_val] at h
    exact h
  refine ⟨k⁻¹*radicalElement p,
    (rootGenerated (F:=F)).mul_mem ((rootGenerated (F:=F)).inv_mem hk)
      (radicalSubgroup_le_rootGenerated ⟨p,rfl⟩),s,?_⟩
  change k.val.symm ((radicalElement p).val (oppositeBaseCell (F:=F)).val)=s.val • x
  rw [hp]
  change k.val.symm (s.val • k.val x)=s.val • x
  rw [map_smul,k.val.symm_apply_apply]

theorem whiteZero_vectors_projectively_transitive_generated (x y : Carrier F)
    (hx : x≠0) (ha : adjoint x=0) (ht : trace x=0)
    (hy : y≠0) (hb : adjoint y=0) (hu : trace y=0) :
    ∃g : Model F, g∈rootGenerated ∧ ∃s : Fˣ,g.val x=s.val • y := by
  obtain ⟨g,hg,s,hs⟩ := whiteZero_from_base_generated x hx ha ht
  obtain ⟨h,hh,t,ht'⟩ := whiteZero_from_base_generated y hy hb hu
  have hgx : g.val.symm x=(s⁻¹).val • (oppositeBaseCell (F:=F)).val := by
    apply g.val.injective
    rw [g.val.apply_symm_apply,map_smul,hs,smul_smul]
    simp
  refine ⟨h*g⁻¹,(rootGenerated (F:=F)).mul_mem hh ((rootGenerated (F:=F)).inv_mem hg),s⁻¹*t,?_⟩
  change h.val (g.val.symm x)=((s⁻¹*t).val) • y
  rw [hgx,map_smul,ht',smul_smul,Units.val_mul]

instance rootGenerated_whiteZeroPoints_pretransitive :
    MulAction.IsPretransitive (rootGenerated (F:=F)) (WhiteZeroPoints F) where
  exists_smul_eq x y := by
    obtain ⟨g,hg,s,hs⟩ := whiteZero_vectors_projectively_transitive_generated
      x.val.rep y.val.rep (Projectivization.rep_nonzero _) x.prop.2 x.prop.1
      (Projectivization.rep_nonzero _) y.prop.2 y.prop.1
    refine ⟨⟨g,hg⟩,Subtype.ext ?_⟩
    change g.val • x.val=y.val
    rw [←Projectivization.mk_rep x.val,Projectivization.smul_mk,
      ←Projectivization.mk_rep y.val]
    apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
    exact ⟨s,hs.symm⟩

theorem rootGenerated_whiteZeroPoints_transitive :
    MulAction.IsPretransitive (rootGenerated (F:=F)) (WhiteZeroPoints F) := inferInstance

end Atlas.F4
