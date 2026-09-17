import Atlas.Fischer.ParkerLoopIdentities
import Atlas.Algebra.BinaryCocycleSplitting

namespace Atlas.Fischer
open Atlas.Codes

/-- A subcode on which all three actual Parker-loop obstructions vanish. -/
structure ParkerElementarySubcode where
  code : Submodule Bit golay
  square_zero : ∀ a : code, golayQuarterWeight a.val = 0
  commutator_zero : ∀ a b : code, golayHalfOverlap a.val b.val = 0
  associator_zero : ∀ a b c : code,
    parkerTripleIntersection a.val b.val c.val = 0

namespace ParkerElementarySubcode

/-- Source divisibility hypotheses, applied to the retained Golay words. -/
def ofDivisibility (K : Submodule Bit golay)
    (hw : ∀ a : K, 8 ∣ hammingNorm a.val.val)
    (hi : ∀ a b : K, 4 ∣ overlap a.val.val b.val.val)
    (ht : ∀ a b c : K, 2 ∣ parkerTripleCount a.val.val b.val.val c.val.val) :
    ParkerElementarySubcode where
  code := K
  square_zero a := by
    obtain ⟨k, hk⟩ := hw a
    change ((hammingNorm a.val.val / 4 : ℕ) : Bit) = 0
    have he : hammingNorm a.val.val / 4 = 2 * k := by omega
    rw [he, Nat.cast_mul]
    simp
  commutator_zero a b := by
    obtain ⟨k, hk⟩ := hi a b
    change ((overlap a.val.val b.val.val / 2 : ℕ) : Bit) = 0
    have he : overlap a.val.val b.val.val / 2 = 2 * k := by omega
    rw [he, Nat.cast_mul]
    simp
  associator_zero a b c := by
    rw [← parkerTripleCount_cast]
    obtain ⟨k, hk⟩ := ht a b c
    rw [hk, Nat.cast_mul]
    simp

variable (K : ParkerElementarySubcode)

/-- The inverse image itself, not a replacement abstract group. -/
def Preimage := {d : ParkerLoop // d.1 ∈ K.code}

noncomputable instance : Mul K.Preimage := ⟨fun x y =>
  ⟨parkerLoopMultiply x.val y.val, K.code.add_mem x.property y.property⟩⟩
instance : One K.Preimage := ⟨⟨(0, 0), K.code.zero_mem⟩⟩
instance : Inv K.Preimage := ⟨id⟩

@[simp] theorem preimage_mul_val (x y : K.Preimage) :
    (x * y).val = parkerLoopMultiply x.val y.val := rfl
@[simp] theorem preimage_one_val : (1 : K.Preimage).val = (0, 0) := rfl

noncomputable instance : CommGroup K.Preimage where
  mul_assoc x y z := by
    apply Subtype.ext
    change parkerLoopMultiply (parkerLoopMultiply x.val y.val) z.val = _
    rw [parkerLoopMultiply_associator,
      K.associator_zero ⟨x.val.1,x.property⟩ ⟨y.val.1,y.property⟩ ⟨z.val.1,z.property⟩,
      parkerSign_zero]
    rfl
  one_mul x := Subtype.ext (parkerLoopMultiply_one_left x.val)
  mul_one x := Subtype.ext (parkerLoopMultiply_one_right x.val)
  inv_mul_cancel x := by
    apply Subtype.ext
    change parkerLoopMultiply x.val x.val = (0,0)
    rw [parkerLoopMultiply_square,K.square_zero ⟨x.val.1,x.property⟩]
  mul_comm x y := by
    apply Subtype.ext
    change parkerLoopMultiply x.val y.val = _
    rw [parkerLoopMultiply_commutator,
      K.commutator_zero ⟨x.val.1,x.property⟩ ⟨y.val.1,y.property⟩,parkerSign_zero]
    rfl

 theorem preimage_square (x : K.Preimage) : x ^ 2 = 1 := by
  rw [pow_two]
  exact inv_mul_cancel x

/-- The underlying set is the actual code times its two sign choices. -/
def preimageEquiv : K.Preimage ≃ K.code × Bit where
  toFun x := (⟨x.val.1,x.property⟩,x.val.2)
  invFun x := ⟨(x.1.val,x.2),x.1.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

 theorem preimage_card : Nat.card K.Preimage = 2 * Nat.card K.code := by
  rw [Nat.card_congr K.preimageEquiv, Nat.card_prod]
  simp [Nat.card_eq_fintype_card, Bit, ZMod.card, Nat.mul_comm]

/-- The restricted cocycle is obtained from the proved Parker identities. -/
noncomputable def cocycle : Atlas.Algebra.SymmetricBinaryCocycle K.code where
  toFun a b := parkerGolayFactorSet a.val b.val
  zero_left a := parkerGolayFactorSet_zero_left a.val
  symmetric a b := by
    have h := parkerGolayFactorSet_commutator a.val b.val
    rw [K.commutator_zero a b] at h
    exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq _)
  diagonal a := (parkerGolayFactorSet_square a.val).trans (K.square_zero a)
  cocycle a b c := by
    have h := parkerGolayFactorSet_associator a.val b.val c.val
    rw [K.associator_zero a b c] at h
    have he : (parkerGolayFactorSet a.val b.val + parkerGolayFactorSet (a.val+b.val) c.val) +
        (parkerGolayFactorSet b.val c.val + parkerGolayFactorSet a.val (b.val+c.val)) = 0 := by
      simpa only [add_assoc] using h
    exact (eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _)

end ParkerElementarySubcode
end Atlas.Fischer
