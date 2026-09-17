import Atlas.Mathieu.Mathieu22PairAction
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

noncomputable section
namespace Atlas.Codes
open scoped Pointwise
set_option synthInstance.maxHeartbeats 200000

theorem mathieu22Choice_pair {a a' : Omega} {b : Mathieu23Points a}
    {b' : Mathieu23Points a'} {g : Mathieu24CodeModel}
    (ha : g • a = a') (hb : g • b.val = b'.val) :
    g • ({a,b.val} : Set Omega) = ({a',b'.val} : Set Omega) := by
  simp [Set.smul_set_insert,Set.smul_set_singleton,ha,hb]

def mathieu22ChoiceEquiv {a a' : Omega} {b : Mathieu23Points a}
    {b' : Mathieu23Points a'} {g : Mathieu24CodeModel}
    (ha : g • a = a') (hb : g • b.val = b'.val) :
    Mathieu22PointModel a b ≃* Mathieu22PointModel a' b' :=
  (mathieu22FixingEquiv a b).trans
    ((SubMulAction.fixingSubgroupEquivFixingSubgroup (mathieu22Choice_pair ha hb)).trans
      (mathieu22FixingEquiv a' b').symm)

theorem mathieu22ChoiceEquiv_embedding {a a' : Omega} {b : Mathieu23Points a}
    {b' : Mathieu23Points a'} {g : Mathieu24CodeModel}
    (ha : g • a = a') (hb : g • b.val = b'.val) (h : Mathieu22PointModel a b) :
    mathieu22_embedding a' b' (mathieu22ChoiceEquiv ha hb h) =
      g * mathieu22_embedding a b h * g⁻¹ := by
  have he := (mathieu22FixingEquiv a' b').apply_symm_apply
    (SubMulAction.fixingSubgroupEquivFixingSubgroup
      (mathieu22Choice_pair ha hb) (mathieu22FixingEquiv a b h))
  exact congrArg (fun h : fixingSubgroup Mathieu24CodeModel ({a',b'.val} : Set Omega) => h.val) he

def mathieu22ChoicePoints {a a' : Omega} {b : Mathieu23Points a}
    {b' : Mathieu23Points a'} {g : Mathieu24CodeModel}
    (ha : g • a = a') (hb : g • b.val = b'.val) :
    Mathieu22Points a b ≃ Mathieu22Points a' b' :=
  (mathieu22PairPointsEquiv a b).symm.trans
    ((Equiv.ofBijective (SubMulAction.conjMap_ofFixingSubgroup (mathieu22Choice_pair ha hb))
      (SubMulAction.conjMap_ofFixingSubgroup_bijective)).trans
      (mathieu22PairPointsEquiv a' b'))

theorem mathieu22ChoicePoints_coordinate {a a' : Omega} {b : Mathieu23Points a}
    {b' : Mathieu23Points a'} {g : Mathieu24CodeModel}
    (ha : g • a = a') (hb : g • b.val = b'.val) (x : Mathieu22Points a b) :
    (mathieu22ChoicePoints ha hb x).val.val = g • x.val.val := rfl

theorem mathieu22Choice_equivariant {a a' : Omega} {b : Mathieu23Points a}
    {b' : Mathieu23Points a'} {g : Mathieu24CodeModel}
    (ha : g • a = a') (hb : g • b.val = b'.val)
    (h : Mathieu22PointModel a b) (x : Mathieu22Points a b) :
    mathieu22ChoicePoints ha hb (h • x) =
      mathieu22ChoiceEquiv ha hb h • mathieu22ChoicePoints ha hb x := by
  apply Subtype.ext; apply Subtype.ext
  change g • (mathieu22_embedding a b h • x.val.val) =
    mathieu22_embedding a' b' (mathieu22ChoiceEquiv ha hb h) • (g • x.val.val)
  rw [mathieu22ChoiceEquiv_embedding,mul_smul,mul_smul,inv_smul_smul]

theorem mathieu22Choice_exists (a a' : Omega) (b : Mathieu23Points a)
    (b' : Mathieu23Points a') :
    ∃ g : Mathieu24CodeModel, g • a = a' ∧ g • b.val = b'.val := by
  exact (MulAction.is_two_pretransitive_iff.mp mathieu24_double_pretransitive)
    (Ne.symm b.prop) (Ne.symm b'.prop)

end Atlas.Codes
