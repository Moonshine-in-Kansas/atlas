import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.SetTheory.Cardinal.Finite

namespace Atlas.GroupTheory

/-- If a subfamily is transitive under the acting group, an orbit meets all
of that subfamily or none. This form counts indexed families without choosing
representatives in an orbit quotient. -/
theorem orbit_preimage_card_zero_or {G X Y : Type*} [Group G] [MulAction G X]
    (f : Y→X) (P : Y→Prop) (x : X)
    (hsubset : ∀y,f y∈MulAction.orbit G x → P y)
    (htrans : ∀y z,P y → P z → ∃g : G,g • f y=f z) :
    Nat.card {y : Y // f y∈MulAction.orbit G x}=0 ∨
    Nat.card {y : Y // f y∈MulAction.orbit G x}=Nat.card {y : Y // P y} := by
  classical
  by_cases hm : ∃y,f y∈MulAction.orbit G x
  · right
    obtain ⟨y,hy⟩ := hm
    apply Nat.card_congr (Equiv.subtypeEquivRight (fun z => ?_))
    constructor
    · exact hsubset z
    · intro hz
      obtain ⟨g,hg⟩ := htrans y z (hsubset y hy) hz
      rw [←hg]
      exact MulAction.mapsTo_smul_orbit g x hy
  · left
    have : IsEmpty {y : Y // f y∈MulAction.orbit G x} :=
      ⟨fun y => hm ⟨y.val,y.prop⟩⟩
    exact Nat.card_of_isEmpty

end Atlas.GroupTheory
