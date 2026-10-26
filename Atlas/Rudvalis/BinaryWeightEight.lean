import Atlas.Rudvalis.BinaryMinimum

/-! Exact classification and count of the seven weight-eight residue words. -/
namespace Atlas.Rudvalis

def rowWord (p : Point) : BinaryWord := fun z => if z.1=p then 1 else 0

theorem rowWord_weight (p : Point) : hammingNorm (rowWord p) = 8 := by
  decide +kernel +revert

theorem rowWord_injective : Function.Injective rowWord := by
  intro p q h
  by_contra hpq
  have hh := congrFun h (p,0)
  simp [rowWord,hpq] at hh

theorem binaryResidue_weight_eight_iff (w : BinaryWord) (hw : w ∈ binaryResidue) :
    hammingNorm w = 8 ↔ ∃ p, w = rowWord p := by
  classical
  constructor
  · intro hweight
    obtain ⟨a,rfl⟩ := hw
    obtain ⟨hM,hc⟩ := binaryNormalMap_small_parameters a (by omega)
    have ha : a = (a.1,0,0) := Prod.ext rfl (Prod.ext hM hc)
    have he : hammingNorm a.1 = 1 := by
      rw [ha, binaryNormalMap_constant_weight] at hweight
      omega
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp he
    have hsupport (q : Point) : a.1 q ≠ 0 ↔ q=p := by
      have := Finset.ext_iff.mp hp q
      simpa using this
    refine ⟨p, ?_⟩
    rw [ha]
    funext z
    have hv : a.1 z.1 = if z.1=p then 1 else 0 := by
      by_cases hz : z.1=p
      · have hn := (hsupport z.1).mpr hz
        rcases Atlas.Codes.bit_cases (a.1 z.1) with h | h
        · exact (hn h).elim
        · simpa only [if_pos hz] using h
      · have hh : a.1 z.1 = 0 := by simpa using mt (hsupport z.1).mp hz
        simp [hh,hz]
    simpa [binaryNormalMap,rowWord,theta,quadratic,matrixAt,dot,eta] using hv
  · rintro ⟨p,rfl⟩
    exact rowWord_weight p

noncomputable def weightEightEquiv :
    Point ≃ {w : binaryResidue // hammingNorm w.val = 8} :=
  Equiv.ofBijective (fun p => ⟨⟨rowWord p,binaryResidue_row_word p 1⟩,rowWord_weight p⟩) (by
    constructor
    · intro p q h
      exact rowWord_injective (congrArg (fun w => w.val.val) h)
    · intro w
      obtain ⟨p,hp⟩ := (binaryResidue_weight_eight_iff w.val.val w.val.prop).mp w.prop
      refine ⟨p, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hp.symm)

theorem binaryResidue_weight_eight_count :
    Nat.card {w : binaryResidue // hammingNorm w.val = 8} = 7 := by
  rw [← Nat.card_congr weightEightEquiv]
  simp [Nat.card_eq_fintype_card]

end Atlas.Rudvalis
