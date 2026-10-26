import Atlas.Rudvalis.LatticeMinimum
import Atlas.Rudvalis.LatticeShellLifts

/-! Exhaustion of the actual norm-four shell by coordinate vectors and minimum code lifts. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

theorem integer_symbol_equality_unique (n : ℤ)
    (he : (euclideanSymbolWeight (n : ZMod 4) : ℤ)=n^2) (hn : (n : ZMod 4)≠2) :
    n=integerRepresentative (n : ZMod 4) := by
  have hb : (euclideanSymbolWeight (n : ZMod 4) : ℤ)≤4 := by
    have h : ∀ a : ZMod 4,euclideanSymbolWeight a≤4 := by decide +kernel
    exact_mod_cast h (n : ZMod 4)
  have hl : -2≤n := by nlinarith
  have hu : n≤2 := by nlinarith
  interval_cases n <;> revert hn <;> decide +kernel

theorem integer_minimum_nonzero_residue (z : IntegerCoordinates)
    (hz : reduceModFour z∈quaternaryCode) (hn : (∑ i,z i^2)=16) (hr : reduceModFour z≠0) :
    euclideanWeight (reduceModFour z)=16 ∧ z=integerLift (reduceModFour z) := by
  have hlo := quaternaryCode_minimum (reduceModFour z) hz hr
  have hhi := integer_residue_weight_le z
  rw [hn] at hhi
  have hweight : euclideanWeight (reduceModFour z)=16 := by omega
  refine ⟨hweight,?_⟩
  have hsum : (∑ i,(euclideanSymbolWeight (z i : ZMod 4) : ℤ))=∑ i,z i^2 := by
    change (euclideanWeight (reduceModFour z) : ℤ)=_
    rw [hweight,hn]
    norm_num
  have he := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i∈Finset.univ) => integer_residue_symbol_weight_le (z i))).mp hsum
  have htwo := quaternary_minimum_no_twos (reduceModFour z) hz hweight
  funext i
  exact integer_symbol_equality_unique (z i) (he i (Finset.mem_univ i)) (htwo i)

theorem integer_minimum_zero_residue (z : IntegerCoordinates)
    (hn : (∑ i,z i^2)=16) (hr : reduceModFour z=0) :
    ∃ i : Coordinate,z=Pi.single i 4 ∨ z=Pi.single i (-4) := by
  classical
  have hi : ∃ i,z i≠0 := by
    by_contra h
    push Not at h
    simp [h] at hn
  obtain ⟨i,hi⟩ := hi
  have hc : (z i : ZMod 4)=0 := congrFun hr i
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (z i) 4).mp hc
  have hk0 : k≠0 := by intro h; simp [h] at hk; exact hi hk
  have hkpos : 0<k^2 := sq_pos_of_ne_zero hk0
  have hkge : 1≤k^2 := by omega
  have hlo : 16≤z i^2 := by rw [hk]; norm_num; nlinarith
  have hhi : z i^2≤16 := hn ▸ Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  have he : z i^2=16 := le_antisymm hhi hlo
  have hrest : (∑ j∈Finset.univ.erase i,z j^2)=0 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i),hn,he,sub_self]
  have hz (j : Coordinate) (hj : j≠i) : z j=0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (z j))).mp hrest j (by simp [hj])
    exact sq_eq_zero_iff.mp h
  have hs : z=Pi.single i (z i) := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj,hz j hj]
  have hi4 : z i=4 ∨ z i= -4 := (sq_eq_sq_iff_eq_or_eq_neg).mp (by norm_num; exact he)
  refine ⟨i,?_⟩
  rcases hi4 with h|h
  · exact Or.inl (hs.trans (by rw [h]))
  · exact Or.inr (hs.trans (by rw [h]))

theorem rudvalisLattice_shell_cases (v : RationalSpace) (hv : v∈rudvalisLattice)
    (hn : rationalDot v v=4) :
    (∃ i : Coordinate,v=coordinateMinimum i ∨ v= -coordinateMinimum i) ∨
    ∃ w : MinimumWords,v=halfCoordinates (integerLift w.val.val) := by
  obtain ⟨z,hz,rfl⟩ := (rudvalisLattice_mem v).mp hv
  have hnz : (∑ i,z i^2)=16 := by
    rw [rationalDot_half] at hn
    have he : integerDot z z=∑ i,z i^2 := by simp [integerDot,pow_two]
    rw [he] at hn
    have hq : ((∑ i,z i^2 : ℤ) : ℚ)=16 := by linarith
    exact_mod_cast hq
  by_cases hr : reduceModFour z=0
  · obtain ⟨i,hi|hi⟩ := integer_minimum_zero_residue z hnz hr
    · refine Or.inl ⟨i,Or.inl ?_⟩
      rw [hi]
      funext j
      by_cases hj : j=i <;> norm_num [halfCoordinates,coordinateMinimum,hj]
    · refine Or.inl ⟨i,Or.inr ?_⟩
      rw [hi]
      funext j
      by_cases hj : j=i <;> norm_num [halfCoordinates,coordinateMinimum,hj]
  · obtain ⟨hw,he⟩ := integer_minimum_nonzero_residue z hz hnz hr
    exact Or.inr ⟨⟨⟨reduceModFour z,hz⟩,hw⟩,congrArg halfCoordinates he⟩

end Atlas.Rudvalis
