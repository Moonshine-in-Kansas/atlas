import Atlas.Rudvalis.BilinearWords
import Mathlib.Logic.Embedding.Set

/-! Exhaustive, disjoint classification of the three normal-form strata. -/
namespace Atlas.Rudvalis

theorem constantOnRows_normal_iff (a : BinaryParameters) :
    constantOnRows (binaryNormalMap a) ↔ a.2.1=0 ∧ a.2.2=0 := by
  constructor
  · intro h
    obtain ⟨s,hs⟩ := (constantOnRows_iff _).mp h
    have he := binaryNormalMap_injective (hs.trans (rowSubsetWord_normal s))
    exact ⟨congrArg (fun a : BinaryParameters => a.2.1) he,
      congrArg (fun a : BinaryParameters => a.2.2) he⟩
  · rintro ⟨hM,hc⟩
    intro p x
    change a.1 p + dot (matrixAt a.2.1 p.val) x + theta p a.2.2 x =
      a.1 p + dot (matrixAt a.2.1 p.val) 0 + theta p a.2.2 0
    simp [hM,hc,matrixAt,dot,theta,eta,quadratic]

theorem hasNonzeroBilinearPart_normal_iff (a : BinaryParameters) :
    hasNonzeroBilinearPart (binaryNormalMap a) ↔ a.2.2=0 ∧ a.2.1≠0 := by
  constructor
  · rintro ⟨ε,M,hM,he⟩
    have h := binaryNormalMap_injective he
    have hc := congrArg (fun a : BinaryParameters => a.2.2) h
    have hm := congrArg (fun a : BinaryParameters => a.2.1) h
    exact ⟨hc.symm,hm ▸ hM⟩
  · rintro ⟨hc,hM⟩
    refine ⟨a.1,a.2.1,hM, ?_⟩
    congr 1
    exact Prod.ext rfl (Prod.ext rfl hc.symm)

theorem hasNonzeroQuadraticPart_normal_iff (a : BinaryParameters) :
    hasNonzeroQuadraticPart (binaryNormalMap a) ↔ a.2.2≠0 := by
  constructor
  · rintro ⟨b,hb,he⟩
    exact binaryNormalMap_injective he ▸ hb
  · intro ha
    exact ⟨a,ha,rfl⟩

theorem binaryResidue_three_strata (w : BinaryWord) (hw : w ∈ binaryResidue) :
    (constantOnRows w ∨ hasNonzeroBilinearPart w ∨ hasNonzeroQuadraticPart w) ∧
    ¬(constantOnRows w ∧ hasNonzeroBilinearPart w) ∧
    ¬(constantOnRows w ∧ hasNonzeroQuadraticPart w) ∧
    ¬(hasNonzeroBilinearPart w ∧ hasNonzeroQuadraticPart w) := by
  obtain ⟨a,rfl⟩ := hw
  rw [constantOnRows_normal_iff,hasNonzeroBilinearPart_normal_iff,
    hasNonzeroQuadraticPart_normal_iff]
  tauto

theorem binaryResidue_weight_sixteen_count :
    Nat.card {w : binaryResidue // hammingNorm w.val = 16} = 1701 := by
  classical
  let P := fun w : binaryResidue => constantOnRows w.val ∧ hammingNorm w.val=16
  let Q := fun w : binaryResidue => hasNonzeroBilinearPart w.val ∧ hammingNorm w.val=16
  let R := fun w : binaryResidue => hasNonzeroQuadraticPart w.val ∧ hammingNorm w.val=16
  have he (w : binaryResidue) : hammingNorm w.val=16 ↔ P w ∨ Q w ∨ R w := by
    have hs := (binaryResidue_three_strata w.val w.prop).1
    dsimp [P,Q,R]
    tauto
  have hd : Disjoint P (fun w => Q w ∨ R w) := by
    rw [Pi.disjoint_iff]
    intro w
    rw [Prop.disjoint_iff]
    have hs := binaryResidue_three_strata w.val w.prop
    dsimp [P,Q,R]
    tauto
  have hd' : Disjoint Q R := by
    rw [Pi.disjoint_iff]
    intro w
    rw [Prop.disjoint_iff]
    have hs := binaryResidue_three_strata w.val w.prop
    dsimp [Q,R]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight he),
    Nat.card_congr (subtypeOrEquiv P (fun w => Q w ∨ R w) hd),Nat.card_sum,
    Nat.card_congr (subtypeOrEquiv Q R hd'),Nat.card_sum]
  change Nat.card {w : binaryResidue // constantOnRows w.val ∧ hammingNorm w.val=16} +
    (Nat.card {w : binaryResidue // hasNonzeroBilinearPart w.val ∧ hammingNorm w.val=16} +
    Nat.card {w : binaryResidue // hasNonzeroQuadraticPart w.val ∧ hammingNorm w.val=16}) = 1701
  rw [binaryConstantRows_weight_sixteen_count,binaryBilinear_weight_sixteen_count,
    binaryQuadratic_weight_sixteen_count]

end Atlas.Rudvalis

