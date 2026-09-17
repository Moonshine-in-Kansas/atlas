import Atlas.GroupTheory.SmallIndexSimple
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

noncomputable section
namespace Atlas.GroupTheory
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- A nontrivial coset action of a simple group is faithful. -/
theorem simple_coset_action_injective (H : Subgroup G) (hi : H.index≠1) :
    Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
  let f := MulAction.toPermHom G (G ⧸ H)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases f.normal_ker.eq_bot_or_eq_top with hk|hk
  · exact hk
  · letI : Subsingleton (G ⧸ H) := ⟨by
      intro x y
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
      have hm : g∈f.ker := by rw [hk]; trivial
      have he : f g=1 := hm
      have hx : g • x=x := congrArg (fun p : Equiv.Perm (G ⧸ H) => p x) he
      exact hx.symm.trans hg⟩
    have hc : Nat.card (G ⧸ H)=1 := Nat.card_unique
    exact (hi ((Subgroup.index_eq_card H).trans hc)).elim

/-- The actual coset permutation representation, marked by five coordinates, yields A5. -/
def simpleOrderSixtyEquivAlt5OfIndexFive (hG : Nat.card G=60) (H : Subgroup G) (hH : H.index=5) :
    G ≃* alternatingGroup (Fin 5) := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  let e : (G ⧸ H) ≃ Fin 5 := Fintype.equivFinOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Subgroup.index_eq_card,hH])
  let p : G →* Equiv.Perm (Fin 5) := e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))
  have hp : Function.Injective p := e.permCongrHom.injective.comp
    (simple_coset_action_injective H (by omega))
  let s := Equiv.Perm.sign.comp p
  have hs : s.ker=⊤ := by
    rcases s.normal_ker.eq_bot_or_eq_top with hh|hh
    · have hi := (MonoidHom.ker_eq_bot_iff s).mp hh
      have hc := Nat.card_le_card_of_injective s hi
      have hu : Nat.card ℤˣ=2 := by simp [Nat.card_eq_fintype_card]
      rw [hG,hu] at hc
      omega
    · exact hh
  let f : G →* alternatingGroup (Fin 5) := p.codRestrict _ (fun g => by
    change s g=1
    exact MonoidHom.mem_ker.mp (hs ▸ Subgroup.mem_top g))
  have hf : Function.Injective f := fun a b he => hp (congrArg Subtype.val he)
  have hc : Nat.card G=Nat.card (alternatingGroup (Fin 5)) := by
    rw [hG,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hc⟩)

end Atlas.GroupTheory
