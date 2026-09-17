import Atlas.Lattices.LeechForm

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

theorem square_sum_parity (z : IntegerCoordinates) :
    integerDot z z % 2 = (∑ i, z i) % 2 := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mp
  change ((integerDot z z : ℤ) : Bit) = ((∑ i, z i : ℤ) : Bit)
  simp only [integerDot,Int.cast_sum,Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  have h := bit_square (z i : Bit)
  simpa [pow_two] using h

theorem zero_residue_norm_divisible (x : IntegerCoordinates) (hx : x ∈ evenGolayLattice)
    (hr : halfResidue x 0 = 0) : 32 ∣ integerDot x x := by
  obtain ⟨y,hc,hs,he⟩ := (mem_evenGolayLattice x).mp hx
  have hy : integerReduction y = 0 := by
    have h : halfResidue x 0 = integerReduction y := by
      ext i; simp [halfResidue,integerReduction,he i]
    rw [← h]; exact hr
  have hp (i : Omega) : y i % 2 = 0 := by
    have h := congrFun hy i
    change ((y i : ℤ) : Bit) = 0 at h
    exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h)
  let z : IntegerCoordinates := fun i => y i / 2
  have hz (i : Omega) : y i = 2 * z i := by have h := hp i; dsimp [z]; omega
  have hsum : (∑ i, y i) = 2 * ∑ i, z i := by simp_rw [hz]; rw [Finset.mul_sum]
  rw [hsum] at hs
  have hpz : integerDot z z % 2 = 0 := by rw [square_sum_parity]; omega
  have hn : integerDot x x = 16 * integerDot z z := by
    simp only [integerDot,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [he i,hz i]; ring
  obtain ⟨k,hk⟩ := Int.dvd_of_emod_eq_zero hpz
  rw [hn,hk]
  exact ⟨k,by ring⟩

theorem even_residue_weight_bound (x : IntegerCoordinates) (hx : x ∈ evenGolayLattice) :
    4 * (hammingNorm (halfResidue x 0) : ℤ) ≤ integerDot x x := by
  rw [hammingNorm_eq_sum,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : halfResidue x 0 i = 0
  · simp [h]; exact mul_self_nonneg (x i)
  · have hp := even_mem_coordinate_even x hx i
    have hn : x i ≠ 0 := by
      intro hz; apply h; simp [halfResidue,integerReduction,hz]
    have hi : x i ≤ -2 ∨ 2 ≤ x i := by omega
    simp only [h,ite_false,Nat.cast_one,mul_one]
    rcases hi with hi | hi <;> nlinarith

theorem leech_raw_minimum (x : IntegerCoordinates) (hx : x ∈ leech) (hne : x ≠ 0) :
    32 ≤ integerDot x x := by
  have hn : 0 < integerDot x x := lt_of_le_of_ne (integerDot_self_nonneg x)
    (Ne.symm (mt (integerDot_self_zero x).mp hne))
  obtain ⟨m,(hm | hm),hp,hc,hs⟩ := (mem_leech x).mp hx
  · subst m
    have he := (even_congruences x).mpr ⟨hp,hc,by simpa using hs⟩
    by_cases hr : halfResidue x 0 = 0
    · obtain ⟨k,hk⟩ := zero_residue_norm_divisible x he hr
      omega
    · have hw := golay_minimum _ hc hr
      have hb := even_residue_weight_bound x he
      have hw' : (8 : ℤ) ≤ (hammingNorm (halfResidue x 0) : ℤ) := by exact_mod_cast hw
      omega
  · subst m
    have hraw : 24 ≤ integerDot x x := by
      have h : (∑ _i : Omega, (1 : ℤ)) ≤ integerDot x x := by
        apply Finset.sum_le_sum
        intro i _
        have hpi := hp i
        have hni : x i ≤ -1 ∨ 1 ≤ x i := by omega
        rcases hni with hni | hni <;> nlinarith
      simpa [Omega,HexIndex] using h
    obtain ⟨k,hk⟩ := leech_norm_divisible x hx
    omega

theorem leech_minimum (x : leech) (hx : x ≠ 0) :
    4 ≤ rationalForm (rationalEmbedding x.val) (rationalEmbedding x.val) := by
  rw [rationalForm_integer]
  have h := leech_raw_minimum x.val x.prop (by intro h; apply hx; exact Subtype.ext h)
  have hq : (32 : ℚ) ≤ (integerDot x.val x.val : ℚ) := by exact_mod_cast h
  linarith

theorem leech_minimum_attained : ∃ x : leech,
    rationalForm (rationalEmbedding x.val) (rationalEmbedding x.val) = 4 := by
  refine ⟨⟨oddGlue ((0,0),0),oddGlue_mem _⟩,?_⟩
  rw [rationalForm_integer,oddGlue_norm]
  norm_num

end Atlas.Lattices
