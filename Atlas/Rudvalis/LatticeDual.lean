import Atlas.Rudvalis.LatticeShellLifts

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

/-- Integral rational pairing dual of the actual lattice. -/
def inLatticeDual (v : RationalSpace) : Prop :=
  ∀ w : RationalSpace,w∈rudvalisLattice → ∃ k : ℤ,rationalDot v w=k

theorem lattice_mem_dual (v : RationalSpace) (hv : v∈rudvalisLattice) : inLatticeDual v :=
  fun w hw => rudvalisLattice_integral v w hv hw

theorem dual_half_coordinates (v : RationalSpace) (hv : inLatticeDual v) :
    ∃ z : IntegerCoordinates,halfCoordinates z=v := by
  classical
  have h : ∀ i : Coordinate,∃ k : ℤ,2*v i=k := by
    intro i
    obtain ⟨k,hk⟩ := hv (coordinateMinimum i) (coordinateMinimum_mem i)
    refine ⟨k,?_⟩
    simpa [rationalDot,coordinateMinimum,Pi.single_apply,mul_comm] using hk
  choose z hz using h
  refine ⟨z,?_⟩
  funext i
  change (z i : ℚ)/2=v i
  rw [←hz i]
  ring

theorem dual_half_residue (z : IntegerCoordinates) (hz : inLatticeDual (halfCoordinates z)) :
    reduceModFour z∈quaternaryCode := by
  rw [←quaternaryCode_self_dual]
  intro w hw
  obtain ⟨k,hk⟩ := hz (halfCoordinates (integerLift w))
    (Submodule.mem_map_of_mem (integerLift_mem w hw))
  rw [rationalDot_half] at hk
  have hi : integerDot z (integerLift w)=4*k := by
    have he : (integerDot z (integerLift w) : ℚ)=4*(k : ℚ) := by linarith
    exact_mod_cast he
  have hc : (integerDot z (integerLift w) : ZMod 4)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr ⟨k,hi⟩
  have he : quaternaryForm (reduceModFour z) w=(integerDot z (integerLift w) : ZMod 4) := by
    conv_lhs => rw [←integerLift_reduce w]
    simp [quaternaryForm,reduceModFour,integerDot,dotProduct]
  rw [quaternaryForm_symmetric,he,hc]

/-- The Construction-A lattice equals its integral pairing dual. -/
theorem rudvalisLattice_self_dual (v : RationalSpace) : inLatticeDual v ↔ v∈rudvalisLattice := by
  constructor
  · intro hv
    obtain ⟨z,rfl⟩ := dual_half_coordinates v hv
    exact Submodule.mem_map_of_mem (dual_half_residue z hv)
  · exact lattice_mem_dual v

end Atlas.Rudvalis
