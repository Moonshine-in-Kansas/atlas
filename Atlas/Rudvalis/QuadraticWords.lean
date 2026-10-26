import Atlas.Rudvalis.QuadraticMinimumCount

/-! Exact count of the quadratic weight-sixteen stratum in the actual residue code. -/
namespace Atlas.Rudvalis
open scoped BigOperators

abbrev QuadraticMinimumParameters := Σ c : Point, Σ M : (transposeContraction c.val).ker,
  {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,M.val,c.val)) = 16}

theorem quadraticMinimumParameters_card : Nat.card QuadraticMinimumParameters = 896 := by
  classical
  rw [Nat.card_sigma]
  have hm (c : Point) : Nat.card (Σ M : (transposeContraction c.val).ker,
      {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,M.val,c.val)) = 16}) = 128 := by
    rw [Nat.card_sigma]
    have he (M : (transposeContraction c.val).ker) :
        Nat.card {ε : Point → Bit // hammingNorm (binaryNormalMap (ε,M.val,c.val)) = 16} = 2 :=
      quadraticConstants_count M.val c.val c.prop (LinearMap.mem_ker.mp M.prop)
    simp_rw [he]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    rw [← Nat.card_eq_fintype_card,transposeContraction_ker_card c.val c.prop]
  simp_rw [hm]
  simp

def hasNonzeroQuadraticPart (w : BinaryWord) : Prop :=
  ∃ a : BinaryParameters, a.2.2 ≠ 0 ∧ binaryNormalMap a = w

noncomputable def quadraticMinimumWordEquiv : QuadraticMinimumParameters ≃
    {w : binaryResidue // hasNonzeroQuadraticPart w.val ∧ hammingNorm w.val = 16} :=
  Equiv.ofBijective (fun a =>
    ⟨⟨binaryNormalMap (a.2.2.val,a.2.1.val,a.1.val),⟨_,rfl⟩⟩,
      ⟨_,a.1.prop,rfl⟩,a.2.2.prop⟩) (by
    constructor
    · rintro ⟨⟨c,hc⟩,⟨M,hM⟩,⟨ε,hε⟩⟩ ⟨⟨d,hd⟩,⟨N,hN⟩,⟨δ,hδ⟩⟩ h
      have he := binaryNormalMap_injective (congrArg (fun w => w.val.val) h)
      have heps := congrArg Prod.fst he
      have hmat := congrArg (fun a : BinaryParameters => a.2.1) he
      have hc' := congrArg (fun a : BinaryParameters => a.2.2) he
      dsimp at heps hmat hc'
      cases hc'; cases hmat; cases heps
      rfl
    · intro w
      obtain ⟨a,hc,ha⟩ := w.prop.1
      have hw : hammingNorm (binaryNormalMap a) = 16 := ha ▸ w.prop.2
      have hM := binaryNormalMap_quadratic_minimum_contraction a hc hw
      refine ⟨⟨⟨a.2.2,hc⟩,⟨a.2.1,hM⟩,⟨a.1,hw⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact ha)

theorem binaryQuadratic_weight_sixteen_count :
    Nat.card {w : binaryResidue // hasNonzeroQuadraticPart w.val ∧ hammingNorm w.val = 16} = 896 := by
  rw [← Nat.card_congr quadraticMinimumWordEquiv]
  exact quadraticMinimumParameters_card

end Atlas.Rudvalis
