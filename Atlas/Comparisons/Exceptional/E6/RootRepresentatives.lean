import Atlas.Comparisons.Exceptional.E6.RootReduction

/-! Explicit representatives of the opposite root pairs. All norm and residue
claims below are checked in Lean over the full specified finite domains. -/
namespace Atlas.Comparisons.E6Lattice

def rootRepresentative : Fin 36 → (Fin 6 → ℤ) :=
  ![![0,0,0,0,0,1],
    ![0,0,0,0,1,0],
    ![0,0,0,1,0,0],
    ![0,0,0,1,1,0],
    ![0,0,1,0,0,0],
    ![0,0,1,0,0,1],
    ![0,0,1,1,0,0],
    ![0,0,1,1,0,1],
    ![0,0,1,1,1,0],
    ![0,0,1,1,1,1],
    ![0,1,0,0,0,0],
    ![0,1,1,0,0,0],
    ![0,1,1,0,0,1],
    ![0,1,1,1,0,0],
    ![0,1,1,1,0,1],
    ![0,1,1,1,1,0],
    ![0,1,1,1,1,1],
    ![0,1,2,1,0,1],
    ![0,1,2,1,1,1],
    ![0,1,2,2,1,1],
    ![1,0,0,0,0,0],
    ![1,1,0,0,0,0],
    ![1,1,1,0,0,0],
    ![1,1,1,0,0,1],
    ![1,1,1,1,0,0],
    ![1,1,1,1,0,1],
    ![1,1,1,1,1,0],
    ![1,1,1,1,1,1],
    ![1,1,2,1,0,1],
    ![1,1,2,1,1,1],
    ![1,1,2,2,1,1],
    ![1,2,2,1,0,1],
    ![1,2,2,1,1,1],
    ![1,2,2,2,1,1],
    ![1,2,3,2,1,1],
    ![1,2,3,2,1,2]]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Check each of the36 explicit integral vectors.
theorem rootRepresentative_norm (i : Fin 36) : norm (rootRepresentative i) = 1 := by
  revert i
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Check all64 binary vectors against the36 displayed lifts.
theorem binary_root_lift (v : Fin 6 → ZMod 2) (hv : norm v = 1) :
    ∃ i : Fin 36, reduceBinary (rootRepresentative i) = v := by
  revert v
  decide

theorem root_representative_exhaustion (x : Fin 6 → ℤ) (hx : norm x = 1) :
    ∃ i : Fin 36, x = rootRepresentative i ∨ x = -rootRepresentative i := by
  have hv : norm (reduceBinary x) = 1 := by rw [norm_reduceBinary,hx]; rfl
  obtain ⟨i,hi⟩ := binary_root_lift (reduceBinary x) hv
  exact ⟨i,root_reduction_pair (rootRepresentative i) x (rootRepresentative_norm i) hx hi⟩

end Atlas.Comparisons.E6Lattice
