import Atlas.Conway.EisensteinNineHexadFamily
import Atlas.Conway.EisensteinHexadPhaseCoordinateNorms
import Atlas.Lattices.EisensteinFrameVectorMembership

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinNineHexadVector_heavy_norm (s : Finset (Fin 12))
    (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s) (b : ZMod 3) (hb : b≠0) :
    (eisensteinNineHexadVector s k j b j).norm=9 := by
  have hjk : j≠k := by intro h; exact hj (h ▸ hk)
  have hf : ∀ b : ZMod 3,b≠0 →
      (eisensteinTheta*(-(eisensteinTheta*eisensteinPhaseCorrection b))).norm=9 := by decide +kernel
  simpa [eisensteinNineHexadVector,eisensteinNineHexadLift,Pi.smul_apply,smul_eq_mul,hj,hjk]
    using hf b hb

/-- Each frame in a counted constant norm-nine family has an actual norm-nine coordinate witness. -/
theorem eisensteinNineHexadFamily_nine_witness (b : ZMod 3) (hb : b≠0)
    (F : EisensteinFrame) (hF : F ∈ eisensteinNineHexadFamily b hb) :
    ∃ x ∈ eisensteinFrameVectors F,∃ j : Fin 12,(x.val.val j).norm=9 := by
  classical
  obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
  obtain ⟨t,ht⟩ := (eisensteinNineHexadPairOrbit_mem b hb p F).mp hp
  let y := eisensteinNineHexadShellVector _ (eisensteinHexadPairSupport_mem p)
    _ _ (eisensteinHexadPairPoint_mem p) (eisensteinNineHexadPairOutside_mem p) b hb
  let x := eisensteinShellAction (eisensteinPhaseIsometries t) 6 y
  have hx : eisensteinFrameOfVector x=F := by
    rw [← eisensteinFrameAction_vector]
    exact ht
  refine ⟨x,(eisensteinFrameOfVector_eq_iff_mem x F).mp hx,eisensteinNineHexadPairOutside p,?_⟩
  change ((eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t.toAdd)) y.val).val
    (eisensteinNineHexadPairOutside p)).norm=9
  rw [eisensteinIntegralAction_phase t.toAdd,eisensteinDiagonal_coordinate_norm]
  exact eisensteinNineHexadVector_heavy_norm _ _ _ (eisensteinHexadPairPoint_mem p)
    (eisensteinNineHexadPairOutside_mem p) b hb

/-- The891 heavy family and each2673 norm-nine family are disjoint geometrically. -/
theorem eisensteinHexadFamily_disjoint_nine (b : ZMod 3) (hb : b≠0) :
    Disjoint eisensteinHexadFamily (eisensteinNineHexadFamily b hb) := by
  classical
  apply Finset.disjoint_left.mpr
  intro F hF hG
  obtain ⟨x,hx,j,hj⟩ := eisensteinNineHexadFamily_nine_witness b hb F hG
  obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hF
  obtain ⟨t,ht⟩ := (eisensteinHexadPairOrbit_mem p F).mp hp
  rw [← ht] at hx
  have hn := eisensteinHexadPhaseFrame_coordinate_norms _ (eisensteinHexadPairSupport_mem p)
    _ (eisensteinHexadPairPoint_mem p) t.toAdd x hx j
  rcases hn with hn|hn|hn <;> omega

end Atlas.Conway
