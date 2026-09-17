import Atlas.Lattices.EisensteinHexadLines

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes

/-- All72 vectors of a constant-heavy hexad frame have only scalar norms0,3,12. -/
theorem eisensteinHexadFrame_coordinate_norms (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s)
    (x : EisensteinShell 6) (hx : x ∈ eisensteinFrameVectors (eisensteinHexadFrame s hs i hi))
    (k : Fin 12) : (x.val.val k).norm=0 ∨ (x.val.val k).norm=3 ∨ (x.val.val k).norm=12 := by
  classical
  have hL := (eisensteinFrameLines_recovers_vectors _ x).mpr hx
  rw [eisensteinHexadFrame_lines] at hL
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hL
  obtain ⟨u,hu⟩ := eisenstein_six_sameLine_unit
    (eisensteinHexadSideVector s hs j).val x.val
    (eisensteinHexadSideVector s hs j).property x.property
    ((eisensteinScalarLine_eq_iff _ _).mp hj.symm)
  have hn := congrArg (fun y : EisensteinLattice => (y.val k).norm) hu
  change (x.val.val k).norm=((u : Eisenstein)*(eisensteinHexadSideVector s hs j).val.val k).norm at hn
  rw [map_mul,(eisenstein_isUnit_iff (u : Eisenstein)).mp u.isUnit,one_mul] at hn
  rw [hn]
  unfold eisensteinHexadSideVector
  split_ifs with hjs
  · change (eisensteinHexadVector s j k).norm=0 ∨
      (eisensteinHexadVector s j k).norm=3 ∨ (eisensteinHexadVector s j k).norm=12
    rw [eisensteinHexadVector_coordinate_norm s j hjs k]
    split_ifs <;> simp
  · change (eisensteinHexadVector sᶜ j k).norm=0 ∨
      (eisensteinHexadVector sᶜ j k).norm=3 ∨ (eisensteinHexadVector sᶜ j k).norm=12
    rw [eisensteinHexadVector_coordinate_norm sᶜ j (Finset.mem_compl.mpr hjs) k]
    split_ifs <;> simp

end Atlas.Lattices
