import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Ring

namespace Atlas

/-- Restricting an action embeds its point stabilizer into the ambient point stabilizer. -/
def subgroupStabilizerHom {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (x : X) : MulAction.stabilizer H x →* MulAction.stabilizer G x where
  toFun g := ⟨g.val.val,g.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem subgroupStabilizerHom_injective {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (x : X) : Function.Injective (subgroupStabilizerHom H x) := by
  intro g h he
  have hh : g.val.val=h.val.val := congrArg (fun u : MulAction.stabilizer G x=>u.val) he
  exact Subtype.ext (Subtype.ext hh)

/-- A stabilizer bound yields divisibility of each restricted orbit, without transitivity assumptions. -/
theorem suborbit_card_divisible {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (H : Subgroup G) (x : X) (n : ℕ)
    (hcard : Nat.card H=n*Nat.card (MulAction.stabilizer G x)) :
    n∣Nat.card (MulAction.orbit H x) := by
  have hd := Subgroup.card_dvd_of_injective (subgroupStabilizerHom H x)
    (subgroupStabilizerHom_injective H x)
  obtain ⟨k,hk⟩ := hd
  have ho := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H x)
  rw [Nat.card_prod,hcard,hk] at ho
  refine ⟨k,?_⟩
  apply Nat.mul_right_cancel (Nat.card_pos (α:=MulAction.stabilizer H x))
  calc
    Nat.card (MulAction.orbit H x)*Nat.card (MulAction.stabilizer H x)=
        n*(Nat.card (MulAction.stabilizer H x)*k) := ho
    _=(n*k)*Nat.card (MulAction.stabilizer H x) := by ring

end Atlas
