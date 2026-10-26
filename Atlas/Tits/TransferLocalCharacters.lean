import Atlas.Tits.TransferDefinition
import Atlas.Tits.TransferRowCentralizer
import Atlas.GroupTheory.StabilizerCharacterTransport

namespace Atlas.Tits
open Atlas.GroupTheory Atlas.Rudvalis

noncomputable def neighbourTransporter (v : Neighbours) : Ambient :=
  Classical.choose (MulAction.exists_smul_eq Ambient referenceNeighbour v)

theorem neighbourTransporter_spec (v : Neighbours) :
    neighbourTransporter v • referenceNeighbour = v :=
  Classical.choose_spec (MulAction.exists_smul_eq Ambient referenceNeighbour v)

/-- The intrinsic character on each geometric point stabilizer. -/
noncomputable def multiplierAt (v : Neighbours) :
    MulAction.stabilizer Ambient v →* (ZMod 5)ˣ :=
  fiveQuartetMultiplier.comp
    (stabilizerTransportHom referenceNeighbour v (neighbourTransporter v)
      (neighbourTransporter_spec v))

theorem multiplierAt_eq_transport (v : Neighbours) (r : Ambient)
    (hr : r • referenceNeighbour = v) (a : MulAction.stabilizer Ambient v) :
    multiplierAt v a = fiveQuartetMultiplier
      (stabilizerTransportHom referenceNeighbour v r hr a) :=
  stabilizer_character_independent referenceNeighbour v fiveQuartetMultiplier
    (neighbourTransporter v) r (neighbourTransporter_spec v) hr a

theorem multiplierAt_reference (a : pairStabilizer) :
    multiplierAt referenceNeighbour a = fiveQuartetMultiplier a := by
  rw [multiplierAt_eq_transport referenceNeighbour 1 (one_smul _ _) a]
  congr 1
  apply Subtype.ext
  simp [stabilizerTransportHom]

theorem multiplierAt_conjugate (v : Neighbours) (g : Ambient)
    (a : MulAction.stabilizer Ambient v) :
    multiplierAt (g • v) ⟨g*a.val*g⁻¹,by
      change (g*a.val*g⁻¹) • (g • v)=g • v
      rw [mul_smul,mul_smul,inv_smul_smul,a.prop]⟩ = multiplierAt v a := by
  rw [multiplierAt_eq_transport (g • v) (g*neighbourTransporter v)
    (by rw [mul_smul,neighbourTransporter_spec])]
  exact stabilizer_character_conjugate referenceNeighbour v fiveQuartetMultiplier
    (neighbourTransporter v) g (neighbourTransporter_spec v) a

/-- Centralizing transport gives equal local characters for the same element. -/
theorem multiplierAt_centralizing_transport (v w : Neighbours) (k g : Ambient)
    (hv : k • v=v) (hw : k • w=w) (hc : Commute g k) (hg : g • v=w) :
    multiplierAt v ⟨k,hv⟩ = multiplierAt w ⟨k,hw⟩ := by
  subst w
  have h := multiplierAt_conjugate v g (⟨k,hv⟩ : MulAction.stabilizer Ambient v)
  have he : g*k*g⁻¹=k := by rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one]
  simpa only [he] using h.symm

/-- The alpha² character is constant on each external coordinate row. -/
theorem multiplierAt_alpha_square_row_constant (p : Point) (hp : p ≠ rowLabel 0)
    (v w : Neighbours) (hv : v.val ∈ coordinateRowFrame p)
    (hw : w.val ∈ coordinateRowFrame p)
    (hfv : localAlpha^2 • v=v) (hfw : localAlpha^2 • w=w) :
    multiplierAt v ⟨localAlpha^2,hfv⟩ = multiplierAt w ⟨localAlpha^2,hfw⟩ := by
  obtain ⟨g,hg,ht⟩ := alphaSquare_centralizer_row_transitive p hp v w hv hw
  exact multiplierAt_centralizing_transport v w (localAlpha^2) g hfv hfw hg ht

/-- Each two-cycle character squares to one, since alpha has order dividing four. -/
theorem multiplierAt_alpha_square_square (v : Neighbours) (hv : localAlpha^2 • v=v) :
    (multiplierAt v ⟨localAlpha^2,hv⟩)^2 = 1 := by
  rw [←map_pow]
  have he : (⟨localAlpha^2,hv⟩ : MulAction.stabilizer Ambient v)^2=1 := by
    apply Subtype.ext
    change (localAlpha^2)^2=1
    rw [←pow_mul]
    exact localAlpha_fourth
  rw [he,map_one]

end Atlas.Tits
