import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Blocks

namespace Atlas.GroupTheory
open MulAction

/-- A simple point stabilizer which is not normal forces faithfulness. -/
theorem faithful_of_simple_stabilizer_not_normal {G X : Type*} [Group G]
    [MulAction G X] (a : X) [IsSimpleGroup (stabilizer G a)]
    (hn : ¬ (stabilizer G a).Normal) : FaithfulSMul G X := by
  let K := stabilizer G a
  let f := toPermHom G X
  let N := f.ker
  have hNK : N ≤ K := by
    intro g hg
    have he : f g = 1 := hg
    exact congrArg (fun p : Equiv.Perm X => p a) he
  have hN : N = ⊥ := by
    rcases (inferInstance : (N.subgroupOf K).Normal).eq_bot_or_eq_top with hb | ht
    · apply bot_unique
      intro g hg
      have hm : (⟨g,hNK hg⟩ : K) ∈ N.subgroupOf K := hg
      rw [hb,Subgroup.mem_bot] at hm
      exact congrArg Subtype.val hm
    · exfalso
      apply hn
      have hKN : K ≤ N := by
        intro g hg
        have hm : (⟨g,hg⟩ : K) ∈ N.subgroupOf K := by rw [ht]; trivial
        exact hm
      have he : K = N := le_antisymm hKN hNK
      change K.Normal
      rw [he]
      infer_instance
  constructor
  intro g h hgh
  apply (f.ker_eq_bot_iff.mp hN)
  exact Equiv.ext hgh

end Atlas.GroupTheory
