/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Codes.GolayMinimum

namespace Atlas.Codes
open scoped BigOperators

def golayFlatParameters : (Fin 12 → Bit) ≃ₗ[Bit] ((Fin 6 → Bit) × (Fin 5 → Bit) × Bit) where
  toFun t := (![t 0,t 1,t 2,t 3,t 4,t 5], ![t 6,t 7,t 8,t 9,t 10], t 11)
  invFun t := ![t.1 0,t.1 1,t.1 2,t.1 3,t.1 4,t.1 5,
    t.2.1 0,t.2.1 1,t.2.1 2,t.2.1 3,t.2.1 4,t.2.2]
  left_inv := by intro t; funext i; fin_cases i <;> rfl
  right_inv := by
    rintro ⟨h,r,ε⟩
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl
  map_add' := by intros; ext i <;> (try fin_cases i) <;> rfl
  map_smul' := by intros; ext i <;> (try fin_cases i) <;> rfl

noncomputable def golayBasis : Module.Basis (Fin 12) Bit golay :=
  (Pi.basisFun Bit (Fin 12)).map
    ((golayFlatParameters.trans ((hexFlatParameters.trans hexEquiv).prodCongr
      ((parityEquiv 5).prodCongr (LinearEquiv.refl Bit Bit)))).trans golayEquiv)

def golayGenerators : Fin 12 → BinaryWord :=
  ![jWord (hexGenerators 0),
    jWord (hexGenerators 1),
    jWord (hexGenerators 2),
    jWord (hexGenerators 3),
    jWord (hexGenerators 4),
    jWord (hexGenerators 5),
    rho (Pi.single 0 1 + Pi.single 1 1),
    rho (Pi.single 0 1 + Pi.single 2 1),
    rho (Pi.single 0 1 + Pi.single 3 1),
    rho (Pi.single 0 1 + Pi.single 4 1),
    rho (Pi.single 0 1 + Pi.single 5 1),
    eta]

theorem golayBasis_coe (i : Fin 12) : (golayBasis i : BinaryWord) = golayGenerators i := by
  change golayEncoder (((hexFlatParameters.trans hexEquiv).prodCongr
    ((parityEquiv 5).prodCongr (LinearEquiv.refl Bit Bit)))
      (golayFlatParameters ((Pi.basisFun Bit (Fin 12)) i))) = _
  rw [Pi.basisFun_apply]
  revert i
  decide

theorem golayGenerators_weight (i : Fin 12) : hammingNorm (golayGenerators i) = 8 := by
  fin_cases i
  all_goals simp only [golayGenerators, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, Matrix.head_cons, jWord_weight, hexGenerators_weight, rho_weight, eta_weight]
  all_goals decide

theorem golay_octad_basis :
    (∀ i, (golayBasis i : BinaryWord) = golayGenerators i) ∧
      (∀ i, hammingNorm (golayBasis i : BinaryWord) = 8) := by
  refine ⟨golayBasis_coe, ?_⟩
  intro i
  rw [golayBasis_coe, golayGenerators_weight]

def octadWords : Set BinaryWord := {w | w ∈ golay ∧ hammingNorm w = 8}

theorem octads_span : Submodule.span Bit octadWords = golay := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ h => h.1)
  · intro w hw
    have he := golayBasis.sum_repr (⟨w,hw⟩ : golay)
    have hv := congrArg Subtype.val he
    change (∑ i, (golayBasis.repr ⟨w,hw⟩) i • (golayBasis i : BinaryWord)) = w at hv
    rw [← hv]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨(golayBasis i).prop, (golay_octad_basis.2 i)⟩

end Atlas.Codes
