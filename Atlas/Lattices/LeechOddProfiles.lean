import Atlas.Lattices.LeechSigns

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def oddProfileBase (T F : Finset Omega) : IntegerCoordinates :=
  fun i => 1 - (if i ∈ T then 4 else 0) + (if i ∈ F then 4 else 0)

theorem oddProfileBase_parity (T F : Finset Omega) (i : Omega) : oddProfileBase T F i % 2 = 1 := by
  simp only [oddProfileBase]
  split_ifs <;> norm_num

theorem oddProfileBase_residue (T F : Finset Omega) : halfResidue (oddProfileBase T F) 1 = 0 := by
  ext i
  change (((oddProfileBase T F i - 1) / 2 : ℤ) : Bit) = 0
  simp only [oddProfileBase]
  split_ifs <;> decide

theorem oddProfileBase_sum (T F : Finset Omega) :
    (∑ i, oddProfileBase T F i) = 24 - 4 * (T.card : ℤ) + 4 * (F.card : ℤ) := by
  simp [oddProfileBase,Finset.sum_add_distrib,Finset.sum_sub_distrib,Omega,HexIndex,mul_comm]

theorem oddProfileBase_norm (T F : Finset Omega) (hTF : Disjoint T F) :
    integerDot (oddProfileBase T F) (oddProfileBase T F) =
      24 + 8 * (T.card : ℤ) + 24 * (F.card : ℤ) := by
  have h (i : Omega) : oddProfileBase T F i * oddProfileBase T F i =
      1 + (if i ∈ T then 8 else 0) + (if i ∈ F then 24 else 0) := by
    have hn : ¬(i ∈ T ∧ i ∈ F) := fun h => Finset.disjoint_left.mp hTF h.1 h.2
    simp only [oddProfileBase]
    split_ifs <;> norm_num <;> tauto
  simp only [integerDot,h]
  simp [Finset.sum_add_distrib,Omega,HexIndex,mul_comm]

theorem oddProfileBase_mem (T F : Finset Omega) (hp : ((F.card : ℤ) - T.card) % 2 = 1) :
    oddProfileBase T F ∈ leech := by
  apply (mem_leech _).mpr
  refine ⟨1,Or.inr rfl,oddProfileBase_parity T F,?_,?_⟩
  · rw [oddProfileBase_residue]; exact golay.zero_mem
  · rw [oddProfileBase_sum]
    omega

def signedOddProfile (T F : Finset Omega) (c : golay) : IntegerCoordinates :=
  signChange c.val (oddProfileBase T F)

theorem signedOddProfile_mem (T F : Finset Omega) (hp : ((F.card : ℤ) - T.card) % 2 = 1)
    (c : golay) : signedOddProfile T F c ∈ leech :=
  signChange_preserves c.val c.prop _ (oddProfileBase_mem T F hp)

theorem signedOddProfile_norm (T F : Finset Omega) (hTF : Disjoint T F) (c : golay) :
    integerDot (signedOddProfile T F c) (signedOddProfile T F c) =
      24 + 8 * (T.card : ℤ) + 24 * (F.card : ℤ) := by
  rw [signedOddProfile,signChange_dot,oddProfileBase_norm T F hTF]

theorem signedOddProfile_residue (T F : Finset Omega) (c : golay) :
    halfResidue (signedOddProfile T F c) 1 = c.val := by
  rw [signedOddProfile,signChange_odd_residue _ _ (oddProfileBase_parity T F),oddProfileBase_residue,zero_add]

theorem signedOddProfile_code_injective (T F : Finset Omega) : Function.Injective (signedOddProfile T F) := by
  intro c d h
  apply Subtype.ext
  have he := congrArg (fun x => halfResidue x 1) h
  simpa only [signedOddProfile_residue] using he

end Atlas.Lattices
