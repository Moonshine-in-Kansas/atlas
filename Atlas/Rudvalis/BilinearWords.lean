import Atlas.Rudvalis.BilinearMinimum

/-! Symbolic count of the bilinear weight-sixteen stratum. -/
namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def bilinearConstantsEquiv (M : BinaryMatrix) (hM : isBinaryRankOne M) :
    {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,M,0)) = 16} ≃
      (∀ p : Point, {a : Bit // matrixAt M p.val=0 → a=0}) :=
  (Equiv.subtypeEquivRight (fun ε =>
    (binaryNormalMap_bilinear_weight_sixteen ε M ((isBinaryRankOne_iff M).mp hM).1).trans
      (and_iff_right hM))).trans
    (Equiv.subtypePiEquivPi (p := fun (p : Point) (a : Bit) => matrixAt M p.val=0 → a=0))

theorem bilinearConstants_count (M : BinaryMatrix) (hM : isBinaryRankOne M) :
    Nat.card {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,M,0)) = 16} = 16 := by
  classical
  rw [Nat.card_congr (bilinearConstantsEquiv M hM),Nat.card_eq_fintype_card,Fintype.card_pi]
  have hp (p : Point) : Fintype.card {a : Bit // matrixAt M p.val=0 → a=0} =
      if matrixAt M p.val=0 then 1 else 2 := by
    by_cases he : matrixAt M p.val=0 <;> simp [he,Bit]
  simp_rw [hp]
  have he : (∏ p : Point, if matrixAt M p.val=0 then (1 : ℕ) else 2) =
      2^(nonzeroMatrixBlocks M).card := by
    simp [Finset.prod_ite,nonzeroMatrixBlocks]
  rw [he,((isBinaryRankOne_iff M).mp hM).2]
  norm_num

abbrev BilinearMinimumParameters := Σ M : {M : BinaryMatrix // isBinaryRankOne M},
  {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,M.val,0)) = 16}

theorem bilinearMinimumParameters_card : Nat.card BilinearMinimumParameters = 784 := by
  classical
  rw [Nat.card_sigma]
  simp_rw [bilinearConstants_count _ (Subtype.prop _)]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card,binaryRankOne_card]

def hasNonzeroBilinearPart (w : BinaryWord) : Prop :=
  ∃ ε : Point → Bit, ∃ M : BinaryMatrix, M ≠ 0 ∧ binaryNormalMap (ε,M,0) = w

noncomputable def bilinearMinimumWordEquiv : BilinearMinimumParameters ≃
    {w : binaryResidue // hasNonzeroBilinearPart w.val ∧ hammingNorm w.val = 16} :=
  Equiv.ofBijective (fun a =>
    ⟨⟨binaryNormalMap (a.2.val,a.1.val,0),⟨_,rfl⟩⟩,
      ⟨_,_,((isBinaryRankOne_iff _).mp a.1.prop).1,rfl⟩,a.2.prop⟩) (by
    constructor
    · rintro ⟨⟨M,hM⟩,⟨ε,hε⟩⟩ ⟨⟨N,hN⟩,⟨δ,hδ⟩⟩ h
      have he := binaryNormalMap_injective (congrArg (fun w => w.val.val) h)
      have heps := congrArg Prod.fst he
      have hmat := congrArg (fun a : BinaryParameters => a.2.1) he
      dsimp at heps hmat
      cases hmat; cases heps
      rfl
    · intro w
      obtain ⟨ε,M,hM,ha⟩ := w.prop.1
      have hw : hammingNorm (binaryNormalMap (ε,M,0)) = 16 := ha ▸ w.prop.2
      have hRank := ((binaryNormalMap_bilinear_weight_sixteen ε M hM).mp hw).1
      refine ⟨⟨⟨M,hRank⟩,⟨ε,hw⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact ha)

theorem binaryBilinear_weight_sixteen_count :
    Nat.card {w : binaryResidue // hasNonzeroBilinearPart w.val ∧ hammingNorm w.val = 16} = 784 := by
  rw [← Nat.card_congr bilinearMinimumWordEquiv]
  exact bilinearMinimumParameters_card

end Atlas.Rudvalis
