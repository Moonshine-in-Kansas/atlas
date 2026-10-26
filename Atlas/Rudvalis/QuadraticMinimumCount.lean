import Atlas.Rudvalis.MatrixFibres

/-! Counting the quadratic weight-sixteen words through small local fibres. -/
namespace Atlas.Rudvalis
open scoped BigOperators

theorem blockWeight_minimum_choices (b c : E) (hc : c ≠ 0) :
    Fintype.card {a : Bit // blockWeight a b c =
      (if quadratic c c + dot b c = 1 then 4 else 2)} =
      if quadratic c c + dot b c = 1 then 2 else 1 := by
  decide +kernel +revert

noncomputable def quadraticConstantsEquiv (M : BinaryMatrix) (c : E) (hc : c ≠ 0) :
    {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,M,c)) = 16} ≃
      (∀ p : Point, {a : Bit // blockWeight a (matrixAt M p.val + eta p c) c =
        if p.val=c then 4 else 2}) :=
  (Equiv.subtypeEquivRight (fun ε => binaryNormalMap_quadratic_weight_sixteen (ε,M,c) hc)).trans
    (Equiv.subtypePiEquivPi (p := fun p a =>
      blockWeight a (matrixAt M p.val + eta p c) c = if p.val=c then 4 else 2))

theorem quadraticConstants_count (M : BinaryMatrix) (c : E) (hc : c ≠ 0)
    (hM : matrixAt M.transpose c = 0) :
    Nat.card {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,M,c)) = 16} = 2 := by
  classical
  have hp (p : Point) : Fintype.card {a : Bit //
      blockWeight a (matrixAt M p.val + eta p c) c = (if p.val=c then 4 else 2)} =
      if p.val=c then 2 else 1 := by
    have h := blockWeight_minimum_choices (matrixAt M p.val + eta p c) c hc
    rw [binary_balance_mask,hM] at h
    simpa [dot] using h
  rw [Nat.card_congr (quadraticConstantsEquiv M c hc),Nat.card_eq_fintype_card,Fintype.card_pi]
  simp_rw [hp]
  have he (p : Point) : p.val=c ↔ p=(⟨c,hc⟩ : Point) :=
    ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  simp_rw [he]
  simp

end Atlas.Rudvalis
