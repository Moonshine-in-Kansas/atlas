import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace Atlas.GroupTheory

/-- Summing actual orbits transfers a common divisor to any finite invariant subset. -/
theorem invariant_card_dvd_of_orbits {G X : Type*} [Group G] [MulAction G X]
    (S : Set X) (hfin : S.Finite) (hstable : ∀g : G,∀x∈S,g • x∈S)
    (n : ℕ) (hdiv : ∀x∈S,n∣Nat.card (MulAction.orbit G x)) : n∣Nat.card S := by
  classical
  let : Finite S := hfin.to_subtype
  let : MulAction G S := {
    smul g x := ⟨g • x.val,hstable g x.val x.prop⟩
    one_smul x := Subtype.ext (one_smul G x.val)
    mul_smul g h x := Subtype.ext (mul_smul g h x.val) }
  have horbit (x : S) : Nat.card (MulAction.orbit G x)=Nat.card (MulAction.orbit G x.val) := by
    let e : MulAction.orbit G x ≃ MulAction.orbit G x.val :=
      { toFun := fun y=>⟨y.val.val,by
          obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp y.prop
          exact MulAction.mem_orbit_iff.mpr ⟨g,congrArg Subtype.val hg⟩⟩
        invFun := fun y=>⟨⟨y.val,by
          obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp y.prop
          rw [←hg]
          exact hstable g x.val x.prop⟩,by
          obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp y.prop
          exact MulAction.mem_orbit_iff.mpr ⟨g,Subtype.ext hg⟩⟩
        left_inv := fun _=>rfl
        right_inv := fun _=>rfl }
    exact Nat.card_congr e
  let : Fintype (MulAction.orbitRel.Quotient G S) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G S),Nat.card_sigma]
  exact Finset.dvd_sum fun q _=>by rw [horbit]; exact hdiv q.out.val q.out.prop

end Atlas.GroupTheory
