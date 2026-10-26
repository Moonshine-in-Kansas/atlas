import Atlas.Rudvalis.TorsionWitness
import Mathlib.Data.Fintype.Powerset

/-! The constant-row stratum, counted by subsets rather than code enumeration. -/
namespace Atlas.Rudvalis

def constantOnRows (w : BinaryWord) : Prop := ∀ p x, w (p,x) = w (p,0)

def rowSubsetWord (s : Finset Point) : BinaryWord := fun z => if z.1 ∈ s then 1 else 0

theorem rowSubsetWord_normal (s : Finset Point) :
    rowSubsetWord s = binaryNormalMap ((fun p => if p ∈ s then 1 else 0),0,0) := by
  funext z
  simp [rowSubsetWord,binaryNormalMap,matrixAt,dot,theta,quadratic,eta]

theorem rowSubsetWord_mem (s : Finset Point) : rowSubsetWord s ∈ binaryResidue := by
  rw [rowSubsetWord_normal]
  exact ⟨_,rfl⟩

theorem rowSubsetWord_constant (s : Finset Point) : constantOnRows (rowSubsetWord s) :=
  fun _ _ => rfl

theorem rowSubsetWord_weight (s : Finset Point) : hammingNorm (rowSubsetWord s) = 8*s.card := by
  rw [rowSubsetWord_normal,binaryNormalMap_constant_weight]
  congr 1
  simp [hammingNorm]

theorem rowSubsetWord_injective : Function.Injective rowSubsetWord := by
  intro s t h
  ext p
  have he := congrFun h (p,0)
  by_cases hs : p ∈ s <;> by_cases ht : p ∈ t <;> simp_all [rowSubsetWord]

theorem constantOnRows_iff (w : BinaryWord) :
    constantOnRows w ↔ ∃ s : Finset Point, w = rowSubsetWord s := by
  classical
  constructor
  · intro hw
    refine ⟨Finset.univ.filter (fun p => w (p,0) ≠ 0), ?_⟩
    funext z
    rw [hw z.1 z.2]
    rcases Atlas.Codes.bit_cases (w (z.1,0)) with hz | hz <;> simp [rowSubsetWord,hz]
  · rintro ⟨s,rfl⟩
    exact rowSubsetWord_constant s

noncomputable def constantRowsWeightEquiv (k : ℕ) :
    {s : Finset Point // s.card = k} ≃
      {w : binaryResidue // constantOnRows w.val ∧ hammingNorm w.val = 8*k} :=
  Equiv.ofBijective (fun s => ⟨⟨rowSubsetWord s.val,rowSubsetWord_mem s.val⟩,
    rowSubsetWord_constant s.val, by rw [rowSubsetWord_weight,s.prop]⟩) (by
    constructor
    · intro s t h
      apply Subtype.ext
      exact rowSubsetWord_injective (congrArg (fun w => w.val.val) h)
    · intro w
      obtain ⟨s,hs⟩ := (constantOnRows_iff w.val.val).mp w.prop.1
      have hk : s.card = k := by
        have he := w.prop.2
        rw [hs,rowSubsetWord_weight] at he
        omega
      refine ⟨⟨s,hk⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hs.symm)

theorem binaryConstantRows_count (k : ℕ) :
    Nat.card {w : binaryResidue // constantOnRows w.val ∧ hammingNorm w.val = 8*k} =
      Nat.choose 7 k := by
  rw [← Nat.card_congr (constantRowsWeightEquiv k),Nat.card_eq_fintype_card]
  simp [Fintype.card_finset_len]

theorem binaryConstantRows_weight_sixteen_count :
    Nat.card {w : binaryResidue // constantOnRows w.val ∧ hammingNorm w.val = 16} = 21 := by
  exact binaryConstantRows_count 2

end Atlas.Rudvalis
