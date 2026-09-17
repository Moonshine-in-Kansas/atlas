import Atlas.LinearGroups.G2.LocalNormalizer
import Atlas.GroupTheory.IwasawaStabilizer

namespace Atlas.G2
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

instance model_nontrivial : Nontrivial (Model F) := by
  refine ⟨⟨rootA 0,rootA 1,?_⟩⟩
  exact fun h => zero_ne_one (rootA_injective h)

/-- The concrete singular action and its two-dimensional long-root local subgroup
satisfy the Iwasawa criterion as soon as primitivity has been established. -/
theorem isSimple_of_preprimitive [Finite F] (hq : 2 < Nat.card F)
    [MulAction.IsPreprimitive (Model F) (SingularPoints F)] : IsSimpleGroup (Model F) := by
  letI := isPerfect hq
  exact Atlas.GroupTheory.iwasawa_stabilizer_simple firstPoint longRootLocal
    longRootLocal_le_pointStabilizer longRootLocal_normal_in_pointStabilizer
    longRootLocal_commutative (longRootNormalClosure_eq_top hq)
end Atlas.G2
