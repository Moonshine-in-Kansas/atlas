import Atlas.Rudvalis.FourPlaneSyndrome
import Atlas.Codes.QuaternaryLiftFibres

namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

noncomputable def fourPlaneShortCode (r : Fin 4 → Bit) := supportedCode binaryTorsion (fourPlaneSupport r)

theorem fourPlaneParamMap_torsion_iff (r : Fin 4 → Bit) (hr : (∑ i,r i)=1)
    (v : FourPlaneParameters) : fourPlaneParamMap r v∈binaryTorsion ↔ fourPlaneSyndrome r v=0 := by
  constructor
  · intro hv
    exact hv (signGenerator 16) ⟨_,rfl⟩
  · intro hv
    rintro d ⟨a,rfl⟩
    rw [binaryNormalMap_expansion]
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨j,rfl⟩ := seedGeneratorIndex_surjective i
    change _ * Atlas.Codes.binaryDot (signGenerator j) (fourPlaneParamMap r v)=0
    rw [fourPlaneSyndrome_pairing r hr v j,hv,mul_zero,mul_zero]

noncomputable def fourPlaneShortMap (r : Fin 4 → Bit) (hr : (∑ i,r i)=1) :
    (fourPlaneSyndrome r).ker →ₗ[Bit] fourPlaneShortCode r where
  toFun v := ⟨fourPlaneParamMap r v.val,
    (fourPlaneParamMap_torsion_iff r hr v.val).mpr v.prop,fourPlaneParamMap_supported r v.val⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

noncomputable def fourPlaneShortEquiv (r : Fin 4 → Bit) (hr : (∑ i,r i)=1) :
    (fourPlaneSyndrome r).ker ≃ₗ[Bit] fourPlaneShortCode r :=
  LinearEquiv.ofBijective (fourPlaneShortMap r hr) (by
    constructor
    · intro v w h
      exact Subtype.ext (fourPlaneParamMap_injective r (congrArg Subtype.val h))
    · intro w
      obtain ⟨v,hv⟩ := fourPlaneParamMap_complete r w.val w.prop.1 w.prop.2
      refine ⟨⟨v,(fourPlaneParamMap_torsion_iff r hr v).mp (hv ▸ w.prop.1)⟩,?_⟩
      exact Subtype.ext hv)

theorem fourPlaneSyndrome_surjective (r : Fin 4 → Bit) : Function.Surjective (fourPlaneSyndrome r) := by
  intro a
  refine ⟨a • fourPlaneParameterBasis 0,?_⟩
  rw [map_smul,fourPlaneSyndrome_onto_witness,smul_eq_mul,mul_one]

theorem fourPlaneShortCode_finrank (r : Fin 4 → Bit) (hr : (∑ i,r i)=1) :
    Module.finrank Bit (fourPlaneShortCode r)=5 := by
  rw [← (fourPlaneShortEquiv r hr).finrank_eq]
  have h := LinearMap.finrank_range_add_finrank_ker (fourPlaneSyndrome r)
  rw [LinearMap.range_eq_top.mpr (fourPlaneSyndrome_surjective r),finrank_top] at h
  have hd : Module.finrank Bit FourPlaneParameters=6 := by
    simp [FourPlaneParameters,Module.finrank_prod,Module.finrank_pi_fintype]
  rw [hd,Module.finrank_self] at h
  omega

theorem fourPlaneShortCode_card (r : Fin 4 → Bit) (hr : (∑ i,r i)=1) :
    Nat.card (fourPlaneShortCode r)=32 := by
  classical
  rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=Bit),fourPlaneShortCode_finrank r hr]
  norm_num [Bit,ZMod.card]

end Atlas.Rudvalis
