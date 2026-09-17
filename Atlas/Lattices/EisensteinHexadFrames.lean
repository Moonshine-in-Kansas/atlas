import Atlas.Lattices.EisensteinHexadClasses

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- A constant-hexad frame, using any one of its six heavy vectors. -/
def eisensteinHexadFrame (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinHexadShellVector s hs i hi)

theorem eisensteinHexadFrame_independent (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ s) :
    eisensteinHexadFrame s hs i hi = eisensteinHexadFrame s hs j hj := by
  apply Subtype.ext
  change eisensteinFramePair _ = eisensteinFramePair _
  dsimp only [eisensteinHexadShellVector]
  rw [eisensteinHexadVector_class s hs i j]

theorem eisensteinHexadFrame_compl (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ sᶜ) :
    eisensteinHexadFrame s hs i hi =
      eisensteinHexadFrame sᶜ (ternaryConstantHexads_compl s hs) j hj := by
  apply Subtype.ext
  change eisensteinFramePair _ = eisensteinFramePair _
  dsimp only [eisensteinHexadShellVector]
  rw [eisensteinHexadVector_compl_class s hs i j,eisensteinFramePair_neg]

theorem eisensteinHexadFrame_contains (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ s) :
    eisensteinHexadShellVector s hs j hj ∈
      eisensteinFrameVectors (eisensteinHexadFrame s hs i hi) := by
  simp only [eisensteinFrameVectors,Finset.mem_filter,Finset.mem_univ,true_and]
  change eisensteinClass (eisensteinHexadLatticeVector s hs j) ∈
    eisensteinFramePair (eisensteinClass (eisensteinHexadLatticeVector s hs i))
  rw [eisensteinHexadVector_class s hs j i]
  simp [eisensteinFramePair]

theorem eisensteinHexadFrame_contains_compl (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i j : Fin 12) (hi : i ∈ s) (hj : j ∈ sᶜ) :
    eisensteinHexadShellVector sᶜ (ternaryConstantHexads_compl s hs) j hj ∈
      eisensteinFrameVectors (eisensteinHexadFrame s hs i hi) := by
  rw [eisensteinHexadFrame_compl s hs i j hi hj]
  exact eisensteinHexadFrame_contains _ _ j j hj hj

end Atlas.Lattices
