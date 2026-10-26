import Atlas.Rudvalis.LatticeCoordinates

/-! The actual Construction A lattice has minimum squared norm four. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

theorem integer_residue_symbol_weight_le (n : ℤ) :
    (euclideanSymbolWeight (n : ZMod 4) : ℤ)≤n^2 := by
  have hb : (euclideanSymbolWeight (n : ZMod 4) : ℤ)≤4 := by
    have hh : ∀ a : ZMod 4,euclideanSymbolWeight a≤4 := by decide +kernel
    exact_mod_cast hh (n : ZMod 4)
  by_cases hn : n≤ -2
  · have hs : 4≤n^2 := by nlinarith
    exact hb.trans hs
  by_cases hp : 2≤n
  · have hs : 4≤n^2 := by nlinarith
    exact hb.trans hs
  have hl : -1≤n := by omega
  have hu : n≤1 := by omega
  interval_cases n <;> decide +kernel

theorem integer_residue_weight_le (z : IntegerCoordinates) :
    (euclideanWeight (reduceModFour z) : ℤ)≤∑ i,z i^2 := by
  change ((∑ i,euclideanSymbolWeight (z i : ZMod 4)) : ℤ)≤_
  exact Finset.sum_le_sum (fun i _ => integer_residue_symbol_weight_le (z i))

theorem integer_zero_residue_norm_lower (z : IntegerCoordinates) (hz : reduceModFour z=0)
    (hne : z≠0) : 16≤∑ i,z i^2 := by
  have hi : ∃ i,z i≠0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i,hi⟩ := hi
  have hc : (z i : ZMod 4)=0 := congrFun hz i
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (z i) 4).mp hc
  have hk0 : k≠0 := by intro h; simp [h] at hk; exact hi hk
  have hkpos : 0<k^2 := sq_pos_of_ne_zero hk0
  have hkge : 1≤k^2 := by omega
  have hki : 16≤z i^2 := by rw [hk]; norm_num; nlinarith
  have hsum : z i^2≤∑ j,z j^2 := Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  exact hki.trans hsum

theorem doubledLattice_norm_lower (z : IntegerCoordinates) (hz : reduceModFour z∈quaternaryCode)
    (hne : z≠0) : 16≤∑ i,z i^2 := by
  by_cases hr : reduceModFour z=0
  · exact integer_zero_residue_norm_lower z hr hne
  · have hw := quaternaryCode_minimum (reduceModFour z) hz hr
    have hc : (16 : ℤ)≤(euclideanWeight (reduceModFour z) : ℤ) := by exact_mod_cast hw
    exact hc.trans (integer_residue_weight_le z)

theorem rudvalisLattice_minimum_lower (v : RationalSpace) (hv : v∈rudvalisLattice) (hne : v≠0) :
    4≤rationalDot v v := by
  obtain ⟨z,hz,rfl⟩ := (rudvalisLattice_mem v).mp hv
  have hz0 : z≠0 := by intro h; apply hne; rw [h,map_zero]
  have hl := doubledLattice_norm_lower z hz hz0
  rw [rationalDot_half]
  have he : integerDot z z=∑ i,z i^2 := by simp [integerDot,pow_two]
  rw [he]
  have hq : (16 : ℚ)≤((∑ i,z i^2 : ℤ) : ℚ) := by exact_mod_cast hl
  linarith

theorem rudvalisLattice_minimum_exact :
    (∀ v∈rudvalisLattice,v≠0 → 4≤rationalDot v v) ∧
    ∃ v∈rudvalisLattice,v≠0 ∧ rationalDot v v=4 := by
  refine ⟨rudvalisLattice_minimum_lower,coordinateMinimum (rowLabel 0,0),coordinateMinimum_mem _,?_,coordinateMinimum_norm _⟩
  intro h
  have hn := coordinateMinimum_norm (rowLabel 0,0)
  rw [h] at hn
  norm_num [rationalDot] at hn

end Atlas.Rudvalis
