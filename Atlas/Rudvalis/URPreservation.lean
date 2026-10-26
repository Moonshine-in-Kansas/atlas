import Atlas.Rudvalis.URCertificates

/-! The displayed monomial involutions preserve the actual quaternary code. -/
set_option maxRecDepth 16384
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

theorem involution_preserves_code_of_pivots
    (L : QuaternaryWord →ₗ[ZMod 4] QuaternaryWord)
    (hsq : ∀ w, L (L w)=w)
    (hiso : ∀ v w, quaternaryForm (L v) (L w)=quaternaryForm v w)
    (hres : ∀ i : Fin 19, reduce (L (quaternaryPivot i))∈binaryResidue)
    (hgram : ∀ i j : Fin 19, quaternaryForm (L (quaternaryPivot i)) (quaternaryPivot j)=0) :
    ∀ w, w∈quaternaryCode → L w∈quaternaryCode := by
  have hp (v w : QuaternaryWord) : quaternaryForm (L v) w=quaternaryForm v (L w) := by
    have h := hiso v (L w)
    rw [hsq] at h
    exact h
  apply quaternaryCode_linear_preserves_of_pivots L
  · intro b hb
    apply (quaternaryCode_mem_iff_residue_pivots _).mpr
    have h2 : (2 : ℕ) • double b=0 := by rw [← double_reduce,reduce_double,map_zero]
    have hz : double (reduce (L (double b)))=0 := by
      rw [double_reduce,← map_nsmul,h2,map_zero]
    have hr : reduce (L (double b))=0 := double_injective (hz.trans (map_zero double).symm)
    refine ⟨hr ▸ binaryResidue.zero_mem,?_⟩
    intro i
    rw [hp,double_pairing_zero,binaryForm_symmetric]
    exact hb _ (hres i)
  · intro i
    exact (quaternaryCode_mem_iff_residue_pivots _).mpr ⟨hres i,hgram i⟩

noncomputable def urOperator {R : Type*} [CommRing R] (t : Fin 2) :
    (Coordinate→R) ≃ₗ[R] (Coordinate→R) := if t=0 then rudvalisUOperator else rudvalisROperator

theorem urOperator_transport {R : Type*} [CommRing R] (t : Fin 2) (v : SeedCoordinate→R) :
    urOperator t (seedTransportLinear v)=seedTransportLinear (urSeedOperator t v) := by
  fin_cases t <;> simp [urOperator,urSeedOperator,rudvalisUOperator,rudvalisROperator]

theorem quaternaryPivot_transport (i : Fin 19) :
    quaternaryPivot i=seedTransportLinear (fun z => (pivotOriginal i z : ZMod 4)) := by
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  rw [seedTransportLinear_apply]
  change (signedSeedTransport (pivotOriginal i) (seedCoordinateEquiv (r,k)) : ZMod 4)=_
  rw [signedSeedTransport_apply]
  simp [signedPositionSign]

theorem urSeedOperator_intCast (t : Fin 2) (v : SeedCoordinate→ℤ) :
    urSeedOperator t (fun z => (v z : ZMod 4))=(fun z => (urSeedOperator (R := ℤ) t v z : ZMod 4)) := by
  funext z
  fin_cases t <;> simp only [urSeedOperator,Fin.reduceFinMk,Fin.isValue,ite_true,ite_false,
    show (1 : Fin 2)≠0 by decide,seedUOperator,seedROperator,signedCoordinateOperator,
    LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk]
  all_goals split <;> simp_all

theorem urOperator_pivot_transport (t : Fin 2) (i : Fin 19) :
    urOperator t (quaternaryPivot i)=
      seedTransportLinear (fun z => (urSeedOperator (R := ℤ) t (pivotOriginal i) z : ZMod 4)) := by
  rw [quaternaryPivot_transport,urOperator_transport,urSeedOperator_intCast]

theorem urOperator_pivot_residue (t : Fin 2) (i : Fin 19) :
    reduce (urOperator t (quaternaryPivot i))=
      binaryNormalMap (seedEncodedParameters (urImageParameterCode t i)) := by
  rw [urOperator_pivot_transport]
  funext z
  obtain ⟨⟨r,k⟩,rfl⟩ := seedCoordinateEquiv.surjective z
  change reduceScalar (seedTransportLinear
    (fun z => (urSeedOperator (R := ℤ) t (pivotOriginal i) z : ZMod 4)) (seedCoordinateEquiv (r,k)))=_
  rw [seedTransportLinear_apply]
  have h := urPivot_residue_certificate t i r k
  change _ = binaryNormalMap (seedEncodedParameters (urImageParameterCode t i))
    (rowLabel r,seedInnerLabel r k)
  split_ifs with hk
  · rw [map_neg,map_intCast]
    simpa [signedPositionSign,hk] using h
  · rw [map_intCast]
    simpa [signedPositionSign,hk] using h

theorem urOperator_pivot_pair (t : Fin 2) (i j : Fin 19) :
    quaternaryForm (urOperator t (quaternaryPivot i)) (quaternaryPivot j)=0 := by
  rw [urOperator_pivot_transport,quaternaryPivot_transport]
  change (∑ z,seedTransportLinear _ z * seedTransportLinear _ z)=0
  rw [seedTransportLinear_pairing]
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (∑ z : SeedCoordinate,urSeedOperator (R := ℤ) t (pivotOriginal i) z*pivotOriginal j z) 4).mpr
    (urPivot_pair_certificate t i j)
  simpa only [Int.cast_sum,Int.cast_mul] using h

theorem urOperator_preserves (t : Fin 2) (w : QuaternaryWord) (hw : w∈quaternaryCode) :
    urOperator t w∈quaternaryCode := by
  apply involution_preserves_code_of_pivots (urOperator t).toLinearMap ?_ ?_ ?_ ?_ w hw
  · intro v
    fin_cases t
    · exact rudvalisU_square v
    · exact rudvalisR_square v
  · intro v z
    fin_cases t
    · exact rudvalisU_pairing v z
    · exact rudvalisR_pairing v z
  · intro i
    change reduce (urOperator t (quaternaryPivot i))∈binaryResidue
    rw [urOperator_pivot_residue]
    exact ⟨_,rfl⟩
  · exact urOperator_pivot_pair t

theorem rudvalisU_preserves (w : QuaternaryWord) (hw : w∈quaternaryCode) :
    rudvalisUOperator w∈quaternaryCode := urOperator_preserves 0 w hw

theorem rudvalisR_preserves (w : QuaternaryWord) (hw : w∈quaternaryCode) :
    rudvalisROperator w∈quaternaryCode := urOperator_preserves 1 w hw

theorem rudvalisU_code_iff (w : QuaternaryWord) : rudvalisUOperator w∈quaternaryCode ↔ w∈quaternaryCode := by
  constructor
  · intro h; simpa only [rudvalisU_square] using rudvalisU_preserves _ h
  · exact rudvalisU_preserves w

theorem rudvalisR_code_iff (w : QuaternaryWord) : rudvalisROperator w∈quaternaryCode ↔ w∈quaternaryCode := by
  constructor
  · intro h; simpa only [rudvalisR_square] using rudvalisR_preserves _ h
  · exact rudvalisR_preserves w

end Atlas.Rudvalis
