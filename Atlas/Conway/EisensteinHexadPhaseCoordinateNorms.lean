import Atlas.Lattices.EisensteinHexadCoordinateNorms
import Atlas.Conway.EisensteinHexadPhaseAction

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- The entire72-vector frame of every actual code-phased constant-heavy hexad
still has only scalar coordinate norms0,3,12. -/
theorem eisensteinHexadPhaseFrame_coordinate_norms (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) (t : ternaryGolay)
    (x : EisensteinShell 6)
    (hx : x ∈ eisensteinFrameVectors (eisensteinPhaseIsometries (Multiplicative.ofAdd t) •
      eisensteinHexadFrame s hs i hi)) (k : Fin 12) :
    (x.val.val k).norm=0 ∨ (x.val.val k).norm=3 ∨ (x.val.val k).norm=12 := by
  classical
  rw [eisensteinFrameAction_vectors] at hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hn : ((eisensteinShellAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t)) 6 y).val.val k).norm=
      (y.val.val k).norm := by
    change ((eisensteinIntegralAction _ y.val).val k).norm=_
    rw [eisensteinIntegralAction_phase,eisensteinDiagonal_coordinate_norm]
  rw [hn]
  exact eisensteinHexadFrame_coordinate_norms s hs i hi y hy k

end Atlas.Conway
