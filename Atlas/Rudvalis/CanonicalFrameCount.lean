import Atlas.Rudvalis.IntrinsicIncidenceCounts
import Atlas.Rudvalis.CanonicalFrames

namespace Atlas.Rudvalis
open scoped BigOperators

noncomputable def canonicalBaseMap : IntrinsicQuartets → canonicalBases :=
  fun Q=>⟨canonicalBase Q.val,Q.val,Q.prop,rfl⟩

noncomputable def canonicalBaseMapFiberEquiv (F : canonicalBases) :
    {Q : IntrinsicQuartets // canonicalBaseMap Q=F} ≃ quartetsDetermining F.val :=
  {toFun := fun Q=>⟨Q.val.val,Q.val.prop,congrArg Subtype.val Q.prop⟩
   invFun := fun Q=>⟨⟨Q.val,Q.prop.1⟩,Subtype.ext Q.prop.2⟩
   left_inv := fun _=>rfl
   right_inv := fun _=>rfl}

theorem canonicalBaseMap_fibre_card (F : canonicalBases) :
    Nat.card {Q : IntrinsicQuartets // canonicalBaseMap Q=F}=7 := by
  rw [Nat.card_congr (canonicalBaseMapFiberEquiv F)]
  exact quartetsDetermining_card F.val F.prop

/-- The actual intrinsic canonical-frame count, following the verified seven-quartet fibres. -/
theorem canonicalBases_card : Nat.card canonicalBases=424125 := by
  classical
  let : Fintype canonicalBases := Fintype.ofFinite _
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv canonicalBaseMap)
  rw [Nat.card_sigma,intrinsicQuartets_card] at h
  simp_rw [canonicalBaseMap_fibre_card] at h
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  rw [←Nat.card_eq_fintype_card] at h
  omega

end Atlas.Rudvalis
