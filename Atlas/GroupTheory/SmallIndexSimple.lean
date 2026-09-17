import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.Perm

namespace Atlas.GroupTheory

/-- A proper subgroup of a finite simple group has index large enough for the
faithful coset action. No classification of subgroups is used. -/
theorem subgroup_eq_top_of_index_factorial_lt {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (H : Subgroup G) (hcard : H.index.factorial < Nat.card G) : H=⊤ := by
  classical
  let f := MulAction.toPermHom G (G ⧸ H)
  have hk : f.ker=⊤ := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · have hi := (MonoidHom.ker_eq_bot_iff f).mp h
      have hc := Nat.card_le_card_of_injective f hi
      have he : Nat.card (Equiv.Perm (G ⧸ H)) = H.index.factorial := by
        letI := Fintype.ofFinite (G ⧸ H)
        rw [Nat.card_eq_fintype_card,Fintype.card_perm]
        rw [Subgroup.index_eq_card,Nat.card_eq_fintype_card]
      rw [he] at hc
      omega
    · exact h
  letI : Subsingleton (G ⧸ H) := ⟨by
    intro x y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
    have hm : g ∈ f.ker := by rw [hk]; trivial
    have he : f g = 1 := hm
    have hx : g • x=x := congrArg (fun p : Equiv.Perm (G ⧸ H) => p x) he
    exact hx.symm.trans hg⟩
  apply (Subgroup.index_eq_one).mp
  rw [Subgroup.index_eq_card]
  exact Nat.card_unique

end Atlas.GroupTheory
