import Atlas.LinearGroups.Symplectic.BinarySignKernel
import Atlas.LinearGroups.Symplectic.SmallRankExceptions
import Atlas.LinearGroups.Symplectic.Simplicity

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F] [Finite F]

/-- The field identification is proved from cardinality two. -/
def binaryFieldEquiv (hq : Nat.card F=2) : F ≃+* BinaryException.K := by
  let := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F Nat.prime_two (by simpa only [Nat.card_eq_fintype_card] using hq)).symm

def binaryExceptionEquiv (hq : Nat.card F=2) : Sp 2 BinaryException.K ≃* PSp 2 F :=
  BinaryException.projectionEquiv.trans (fieldEquivPSp (binaryFieldEquiv hq).symm)

/-- A genuine normal subgroup of the actual exceptional central quotient. -/
def exceptionalNormal (hq : Nat.card F=2) : Subgroup (PSp 2 F) :=
  BinaryException.signKernel.map (binaryExceptionEquiv hq).toMonoidHom

instance exceptionalNormal_normal (hq : Nat.card F=2) : (exceptionalNormal hq).Normal :=
  BinaryException.signKernel_normal.map _ (binaryExceptionEquiv hq).surjective

theorem exceptionalNormal_card (hq : Nat.card F=2) : Nat.card (exceptionalNormal hq)=360 := by
  exact (Nat.card_congr ((binaryExceptionEquiv hq).subgroupMap BinaryException.signKernel).toEquiv).symm.trans
    BinaryException.card_signKernel

theorem exceptional_group_card (hq : Nat.card F=2) : Nat.card (PSp 2 F)=720 := by
  rw [card_psp (by decide),hq]
  norm_num [orderNumerator,Finset.prod_range_succ]

theorem exceptionalNormal_ne_bot (hq : Nat.card F=2) : exceptionalNormal hq ≠ ⊥ := by
  intro h
  have hc := exceptionalNormal_card hq
  rw [h] at hc
  simp at hc

theorem exceptionalNormal_ne_top (hq : Nat.card F=2) : exceptionalNormal hq ≠ ⊤ := by
  intro h
  have hc := exceptionalNormal_card hq
  rw [h,Nat.card_congr Subgroup.topEquiv.toEquiv,exceptional_group_card hq] at hc
  omega

/-- The six-quadratic-refinement sign kernel proves the actual (2,2) exception. -/
theorem rank_two_two_not_simple (hq : Nat.card F=2) : ¬ IsSimpleGroup (PSp 2 F) := by
  intro h
  letI := h
  exact (exceptionalNormal_normal hq).eq_bot_or_eq_top.elim
    (exceptionalNormal_ne_bot hq) (exceptionalNormal_ne_top hq)

/-- Exact simplicity range for every symplectic rank and every finite field. -/
theorem simple_iff_good : IsSimpleGroup (PSp n F) ↔ Good n (Nat.card F) := by
  constructor
  · intro hs
    by_cases hn0 : n=0
    · subst n
      exact False.elim (rank_zero_not_simple hs)
    by_cases hn1 : n=1
    · subst n
      left
      refine ⟨rfl,?_⟩
      by_contra hq
      have hq₂ : 1 < Nat.card F := Finite.one_lt_card
      rcases (show Nat.card F=2 ∨ Nat.card F=3 by omega) with h2|h3
      · exact rank_one_two_not_simple h2 hs
      · exact rank_one_three_not_simple h3 hs
    · right
      refine ⟨by omega,?_⟩
      intro he
      have hn : n=2 := congrArg Prod.fst he
      have hq : Nat.card F=2 := congrArg Prod.snd he
      subst n
      exact rank_two_two_not_simple hq hs
  · exact simple_of_good

end Atlas.Symplectic
