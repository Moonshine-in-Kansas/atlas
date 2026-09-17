/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.SextetRecovery

noncomputable section
namespace Atlas.Codes

theorem sextet_coordinate_transitive (x y : Omega) :
    ∃ s : SextetStabilizer, s.val.val x = y := by
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective (Equiv.swap x.1 y.1)
  have hp : g.val.perm x.1 = y.1 := by
    have h := DFunLike.congr_fun hg x.1
    exact h.trans (Equiv.swap_apply_left _ _)
  obtain ⟨t,ht⟩ := hexCoordinate_surjective y.1
    (rowLabel y.2 - g.val.localMap y.1 (rowLabel x.2))
  refine ⟨sextetAffineEquiv ⟨Multiplicative.ofAdd t,g⟩,?_⟩
  rw [sextetAffineEquiv_coordinates]
  change (g.val.perm x.1,rowLabel.symm
    (g.val.localMap (g.val.perm x.1) (rowLabel x.2) + t.val (g.val.perm x.1))) = y
  rw [hp]
  change t.val y.1 = _ at ht
  rw [ht,add_sub_cancel, rowLabel.symm_apply_apply]

theorem golay_coordinate_transitive (x y : Omega) :
    ∃ g : Mathieu24CodeModel, g.val x = y := by
  obtain ⟨s,hs⟩ := sextet_coordinate_transitive x y
  exact ⟨s.val,hs⟩

end Atlas.Codes
