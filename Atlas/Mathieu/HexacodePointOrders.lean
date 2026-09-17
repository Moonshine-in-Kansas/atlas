/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.HexacodePointStabilizer

noncomputable section
namespace Atlas.Codes

instance hexCoordinateAction : MulAction HexAutomorphisms HexIndex :=
  MulAction.compHom HexIndex hexCoordinateHom

theorem hexCoordinateAction_transitive (i j : HexIndex) : ∃ g : HexAutomorphisms, g • i = j := by
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective (Equiv.swap i j)
  refine ⟨g,?_⟩
  change hexCoordinateHom g i = j
  rw [hg,Equiv.swap_apply_left]

def hexPointOrbitEquiv (i : HexIndex) : MulAction.orbit HexAutomorphisms i ≃ HexIndex :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,by
    intro j
    exact ⟨⟨j,MulAction.mem_orbit_iff.mpr (hexCoordinateAction_transitive i j)⟩,rfl⟩⟩

def hexPointOrbitStabilizerEquiv (i : HexIndex) : HexIndex × hexPointStabilizer i ≃ HexAutomorphisms :=
  ((hexPointOrbitEquiv i).symm.prodCongr (Equiv.refl _)).trans
    (MulAction.orbitProdStabilizerEquivGroup HexAutomorphisms i)

theorem hexPointStabilizer_card (i : HexIndex) : Nat.card (hexPointStabilizer i) = 360 := by
  have h := Nat.card_congr (hexPointOrbitStabilizerEquiv i)
  rw [Nat.card_prod,hexAutomorphisms_card] at h
  have hc : Nat.card HexIndex = 6 := by simp [HexIndex]
  rw [hc] at h
  omega

def hexPointKernel (i : HexIndex) : Subgroup (hexPointStabilizer i) := (hexPointLocal i).ker

theorem hexPointKernel_card (i : HexIndex) : Nat.card (hexPointKernel i) = 60 := by
  have h := (hexPointLocal i).ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr (hexPointLocal_surjective i),
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup KIsometry) ≃* KIsometry).toEquiv,
    kIsometry_card,hexPointStabilizer_card] at h
  change Nat.card (hexPointKernel i) * 6 = 360 at h
  omega

end Atlas.Codes
