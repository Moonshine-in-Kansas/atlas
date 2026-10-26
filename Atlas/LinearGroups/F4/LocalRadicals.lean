import Atlas.GroupTheory.LocalSubgroupTransport
import Atlas.LinearGroups.F4.RadicalNormalClosure
import Atlas.LinearGroups.F4.PointTransitivity

/-! The actual local solvable radicals at all white points. Transport is
independent of the chosen group element and compatible with conjugation. -/
noncomputable section
namespace Atlas.F4
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F]

private theorem pointStabilizer_le_radical_normalizer :
    MulAction.stabilizer (Model F) (parabolicPoint (F := F)) ≤
      Subgroup.normalizer (radicalSubgroup (F:=F) : Set (Model F)) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer radicalSubgroup_le_parabolic).mp
    radical_normal_in_pointStabilizer

def localRadical (x : WhiteZeroPoints F) : Subgroup (Model F) :=
  Atlas.GroupTheory.LocalTransport.localAt parabolicPoint radicalSubgroup x

theorem localRadical_eq_of_transport (x : WhiteZeroPoints F) (g : Model F)
    (hg : g • parabolicPoint=x) :
    localRadical x=MulAut.conj g • radicalSubgroup :=
  Atlas.GroupTheory.LocalTransport.localAt_eq_of_transport parabolicPoint radicalSubgroup
    pointStabilizer_le_radical_normalizer x g hg

theorem localRadical_base : localRadical (parabolicPoint (F:=F))=radicalSubgroup :=
  Atlas.GroupTheory.LocalTransport.localAt_base parabolicPoint radicalSubgroup
    pointStabilizer_le_radical_normalizer

theorem localRadical_conj (g : Model F) (x : WhiteZeroPoints F) :
    localRadical (g • x)=MulAut.conj g • localRadical x :=
  Atlas.GroupTheory.LocalTransport.localAt_conj parabolicPoint radicalSubgroup
    pointStabilizer_le_radical_normalizer g x

theorem localRadical_solvable (x : WhiteZeroPoints F) : Group.IsSolvable (localRadical x) := by
  letI := radicalSubgroup_solvable (F:=F)
  exact Atlas.GroupTheory.LocalTransport.localAt_solvable parabolicPoint radicalSubgroup x

theorem localRadical_le_stabilizer (x : WhiteZeroPoints F) :
    localRadical x ≤ MulAction.stabilizer (Model F) x :=
  Atlas.GroupTheory.LocalTransport.localAt_le_stabilizer parabolicPoint radicalSubgroup
    radicalSubgroup_le_parabolic x

theorem localRadical_normal (x : WhiteZeroPoints F) :
    ((localRadical x).subgroupOf (MulAction.stabilizer (Model F) x)).Normal :=
  Atlas.GroupTheory.LocalTransport.localAt_normal parabolicPoint radicalSubgroup
    pointStabilizer_le_radical_normalizer radicalSubgroup_le_parabolic x

theorem localRadical_card (x : WhiteZeroPoints F) : Nat.card (localRadical x)=Nat.card F^15 := by
  change Nat.card (Atlas.GroupTheory.LocalTransport.localAt parabolicPoint radicalSubgroup x)=_
  rw [Atlas.GroupTheory.LocalTransport.card_localAt,card_radicalSubgroup]

theorem localRadical_iSup_eq_top : (⨆x : WhiteZeroPoints F,localRadical x)=⊤ := by
  change (⨆x : WhiteZeroPoints F,
    Atlas.GroupTheory.LocalTransport.localAt parabolicPoint radicalSubgroup x)=⊤
  rw [Atlas.GroupTheory.LocalTransport.localAt_iSup_eq_normalClosure parabolicPoint
    radicalSubgroup pointStabilizer_le_radical_normalizer,radical_normalClosure_eq_top]

end Atlas.F4
