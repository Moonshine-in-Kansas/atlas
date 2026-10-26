import Atlas.Tits.TransferFrobeniusMultipliers
import Atlas.Tits.TransferLocalCharacters
import Atlas.Tits.TransferWitnessCycles

namespace Atlas.Tits
open Atlas.Rudvalis Atlas.GroupTheory
set_option maxRecDepth 16384

/-- The marked coordinates of the three actual Frobenius images. -/
theorem alphaFixedNeighbour_coordinate (n : Fin 3) :
    (alphaFixedNeighbour n).val =
      coordinateCross (originalCoordinateEquiv ((seedTCoord.symm^n.val) (0,2))) := by
  have hp : (codeT^n.val).val.right =
      originalCoordinateEquiv.permCongrHom (seedTCoord.symm^n.val) := by
    change SemidirectProduct.rightHom (codeT.val^n.val) = _
    rw [map_pow]
    have ht : codeT.val.right = originalCoordinateEquiv.permCongrHom seedTCoord.symm :=
      seedConjugateMonomial_right _
    change codeT.val.right^n.val = originalCoordinateEquiv.permCongrHom (seedTCoord.symm^n.val)
    rw [ht,map_pow]
  change (codePointHom pointFrobenius ^ n.val).val • referenceSecondCross = _
  rw [←map_pow]
  change codeGaussianHom (codeT^n.val) • referenceSecondCross = _
  rw [codeGaussianHom_cross,referenceSecondCross_eq,coordinateCross_action]
  have he : (rowLabel 0,binaryLabel 2) = originalCoordinateEquiv (0,2) := rfl
  rw [he,hp,original_congr_apply]

theorem alphaFixedNeighbour_injective : Function.Injective alphaFixedNeighbour := by
  intro n m h
  have hc := congrArg Subtype.val h
  rw [alphaFixedNeighbour_coordinate,alphaFixedNeighbour_coordinate,coordinateCross_eq_iff,
    codeI_coordinate] at hc
  have hsmall : ∀ n m : Fin 3,
      originalCoordinateEquiv ((seedTCoord.symm^n.val) (0,2)) =
        originalCoordinateEquiv ((seedTCoord.symm^m.val) (0,2)) ∨
      ((originalCoordinateEquiv ((seedTCoord.symm^n.val) (0,2))).1,
        (originalCoordinateEquiv ((seedTCoord.symm^n.val) (0,2))).2+
          (originalCoordinateEquiv ((seedTCoord.symm^n.val) (0,2))).1.val) =
        originalCoordinateEquiv ((seedTCoord.symm^m.val) (0,2)) → n=m := by
    decide +kernel
  exact hsmall n m hc

/-- The three marked Frobenius images exhaust all fixed neighbours, by the
 independently established geometric count of three. -/
theorem alphaFixedNeighbour_exhaustion (v : Neighbours) (hv : localAlpha • v=v) :
    ∃n : Fin 3,alphaFixedNeighbour n=v := by
  let f : Fin 3 → {v : Neighbours // localAlpha • v=v} :=
    fun n => ⟨alphaFixedNeighbour n,alphaFixedNeighbour_fixed n⟩
  have hi : Function.Injective f := by
    intro n m h
    exact alphaFixedNeighbour_injective (congrArg Subtype.val h)
  have hs := (hi.bijective_of_nat_card_le (by
    rw [localAlpha_fixed_card,Nat.card_eq_fintype_card,Fintype.card_fin])).2
  obtain ⟨n,hn⟩ := hs ⟨v,hv⟩
  exact ⟨n,congrArg Subtype.val hn⟩

theorem multiplierAt_alphaFixedNeighbour (n : Fin 3) :
    multiplierAt (alphaFixedNeighbour n) ⟨localAlpha,alphaFixedNeighbour_fixed n⟩ = -1 := by
  rw [multiplierAt_eq_transport (alphaFixedNeighbour n) (localFrobenius^n.val) rfl]
  have he : stabilizerTransportHom referenceNeighbour (alphaFixedNeighbour n)
      (localFrobenius^n.val) rfl ⟨localAlpha,alphaFixedNeighbour_fixed n⟩ =
      alphaFrobeniusPair n := by
    apply Subtype.ext
    change (localFrobenius^n.val)⁻¹*localAlpha*localFrobenius^n.val =
      (alphaFrobeniusPair n).val
    exact (alphaFrobeniusPair_underlying n).symm
  rw [he,alphaFrobenius_multiplier]

/-- Every fixed neighbour contributes minus one to the actual transfer. -/
theorem multiplierAt_alpha_fixed (v : Neighbours) (hv : localAlpha • v=v) :
    multiplierAt v ⟨localAlpha,hv⟩ = -1 := by
  obtain ⟨n,rfl⟩ := alphaFixedNeighbour_exhaustion v hv
  exact multiplierAt_alphaFixedNeighbour n

end Atlas.Tits
