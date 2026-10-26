import Atlas.Rudvalis.QuaternarySelfDual
import Atlas.LinearAlgebra.ExponentFour
import Atlas.LinearAlgebra.DoubledAddEquiv

/-! The additive type of the actual self-dual signed-seed code. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open Atlas.LinearAlgebra

noncomputable def quaternaryDoubledEquiv : binaryResidue ≃ Doubled quaternaryCode :=
  Equiv.ofBijective
    (fun d => ⟨⟨double d.val,quaternaryCode_double d.val (binaryResidue_self_orthogonal d.prop)⟩,by
      obtain ⟨q,hq,hd⟩ := (quaternaryCode_residue d.val).mp d.prop
      refine ⟨⟨q,hq⟩,Subtype.ext ?_⟩
      change (2 : ℕ) • q=double d.val
      rw [← double_reduce,hd]⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      apply double_injective
      exact congrArg (fun q : Doubled quaternaryCode => q.val.val) h
    · intro q
      obtain ⟨w,hw⟩ := q.prop
      have hd : reduce w.val∈binaryResidue := (quaternaryCode_residue _).mpr ⟨w.val,w.prop,rfl⟩
      refine ⟨⟨reduce w.val,hd⟩,Subtype.ext (Subtype.ext ?_)⟩
      change double (reduce w.val)=q.val.val
      rw [double_reduce]
      exact congrArg Subtype.val hw)

theorem quaternaryCode_doubled_card : Nat.card (Doubled quaternaryCode)=2^19 := by
  classical
  rw [← Nat.card_congr quaternaryDoubledEquiv,Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := Bit),binaryResidue_finrank]
  rfl

theorem quaternaryCode_exponent_four (q : quaternaryCode) : (4 : ℕ) • q=0 := by
  apply Subtype.ext
  funext z
  change (4 : ℕ) • q.val z=0
  have h : ∀ a : ZMod 4, (4 : ℕ) • a=0 := by decide
  exact h _

theorem quaternaryCode_additive_type :
    Nonempty (quaternaryCode ≃+ ((Fin 19 → ZMod 4) × (Fin 18 → ZMod 2))) := by
  obtain ⟨m,n,⟨e⟩⟩ := exponent_four_decomposition quaternaryCode quaternaryCode_exponent_four
  have hm : m=19 := by
    apply Nat.pow_right_injective (by decide : 2≤2)
    change 2^m=2^19
    rw [← doubled_four_two_card m n,← Nat.card_congr (doubledAddEquiv e),quaternaryCode_doubled_card]
  have hcard := Nat.card_congr e.toEquiv
  rw [quaternaryCode_card,Nat.card_prod] at hcard
  simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod] at hcard
  have hn : n=18 := by
    have hfour : (4 : ℕ)=2^2 := by decide
    rw [hfour,← pow_mul,← pow_add] at hcard
    have he := Nat.pow_right_injective (by decide : 2≤2) hcard
    omega
  subst m
  subst n
  exact ⟨e⟩

noncomputable def quaternaryCodeTypeEquiv :
    quaternaryCode ≃+ ((Fin 19 → ZMod 4) × (Fin 18 → ZMod 2)) :=
  Classical.choice quaternaryCode_additive_type

end Atlas.Rudvalis
