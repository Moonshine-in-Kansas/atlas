import Atlas.Rudvalis.LatticeCrosses
import Atlas.Rudvalis.LatticeShellCount

namespace Atlas.Rudvalis

instance : Finite MinimalShell := Finite.of_equiv _ minimalShellEquiv.symm

theorem rudvalisLattice_minimal_cross_card : Nat.card MinimalCross=4060 := by
  have h := minimalCross_card_mul_four
  rw [rudvalisLattice_minimal_shell_card] at h
  omega

end Atlas.Rudvalis
