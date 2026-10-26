import Atlas.Rudvalis.FourLocalSupports

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
set_option maxRecDepth 16384

theorem reduce_seedTransport_original (v : SeedCoordinate→ZMod 4) (z : SeedCoordinate) :
    reduce (seedTransportLinear v) (originalCoordinateEquiv z)=reduceScalar (v z) := by
  change reduceScalar (seedTransportLinear v (seedCoordinateEquiv (z.1,signedPositionIndex z.2)))=_
  rw [seedTransportLinear_apply]
  have hi : signedPositionIndex (signedPositionIndex z.2)=z.2 := by decide +kernel +revert
  split <;> simp only [hi,map_neg,CharTwo.neg_eq]

theorem fourLocal_normal_original (m : ℕ) (z : SeedCoordinate) :
    binaryNormalMap (fourLocalConstants m,outerMatrix (binaryLabel 1) (binaryLabel 1),0)
      (originalCoordinateEquiv z)=fourLocalMask m z := by
  change fourLocalConstants m (rowLabel z.1)+
    dot (matrixAt (outerMatrix (binaryLabel 1) (binaryLabel 1)) (rowLabel z.1).val)
      (seedInnerLabel z.1 (signedPositionIndex z.2))+
    theta (rowLabel z.1) 0 (seedInnerLabel z.1 (signedPositionIndex z.2))=_
  rw [fourLocalConstants_rows,theta_zero_parameter,add_zero,matrixAt_outer,dot_smul_left]
  unfold fourLocalMask
  rcases Atlas.Codes.bit_cases (dot (binaryLabel 1) (rowLabel z.1).val) with h|h <;> simp [h]

theorem fourLocal_base_support (b : Bool) :
    reduce (monomialHom (if b then fourLocalCodeZ.val else 1) (quaternarySeed (3,0,0,0)))=
      binaryNormalMap (fourLocalBaseConstants b,outerMatrix (binaryLabel 1) (binaryLabel 1),0) := by
  cases b
  · rw [ite_eq_right (by decide),map_one]
    change reduce (quaternarySeed (3,0,0,0))=_
    rw [fourLocalSeed_transport]
    funext z
    obtain ⟨z,rfl⟩ := originalCoordinateEquiv.surjective z
    rw [reduce_seedTransport_original]
    exact (fourLocalOriginal_support_masks z).1.trans (fourLocal_normal_original 70 z).symm
  · rw [ite_eq_left rfl,fourLocalCodeZ_transport,fourLocalSeed_transport]
    change reduce (monomialHom (seedConjugateMonomial fourLocalOriginalZ) (seedTransportLinear fourLocalSeed))=_
    rw [seedConjugateMonomial_transport]
    funext z
    obtain ⟨z,rfl⟩ := originalCoordinateEquiv.surjective z
    rw [reduce_seedTransport_original]
    exact (fourLocalOriginal_support_masks z).2.trans (fourLocal_normal_original 64 z).symm

/-- All eight supports for the base inactive label occur in the actual point stabilizer. -/
theorem fourLocal_fixed_label_support_orbit (δ : Point → Bit)
    (hδ : ∀p,dot (binaryLabel 1) p.val=0 → δ p=0) (hs : (∑p,δ p)=1) :
    ∃g : MulAction.stabilizer codeGroup (coordinateCross (originalCoordinateEquiv (0,1))),
      reduce (monomialHom g.val.val (quaternarySeed (3,0,0,0)))=
        binaryNormalMap (δ,outerMatrix (binaryLabel 1) (binaryLabel 1),0) := by
  obtain ⟨b,B,hB,hδB⟩ := fourLocalConstants_translation δ hδ hs
  obtain ⟨g,hg⟩ := codePermutationHom_surjective ⟨coordinateTranslation B,coordinateTranslation_mem B⟩
  have hgr : g.val.right=coordinateTranslation B := congrArg Subtype.val hg
  have hfix : g • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) := by
    rw [coordinateCross_action,hgr]
    have hc : originalCoordinateEquiv (0,1)=(rowLabel 0,0) := by decide +kernel
    rw [hc]
    change coordinateCross (rowLabel 0,0+matrixAt B (rowLabel 0).val)=_
    rw [hB,zero_add]
  let z : codeGroup := if b then fourLocalCodeZ else 1
  have hz : z • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) := by
    cases b <;> simp only [z,Bool.false_eq_true,ite_false,ite_true,one_smul,fourLocalCode_fix.1]
  refine ⟨⟨g*z,?_⟩,?_⟩
  · change (g*z) • _=_
    rw [mul_smul,hz,hfix]
  · change reduce (monomialHom (g.val*z.val) _)=_
    rw [map_mul]
    change reduce (monomialAction g.val (monomialHom z.val (quaternarySeed (3,0,0,0))))=_
    rw [monomialAction_reduce,hgr]
    have hzv : z.val=(if b then fourLocalCodeZ.val else 1) := by cases b <;> rfl
    rw [hzv,fourLocal_base_support,hδB]
    rfl

end Atlas.Rudvalis
