import Atlas.Rudvalis.FrameGlueHexad
import Atlas.Rudvalis.SeedFrobeniusPermutation

/-! The 24 literal unit/Frobenius hexads span the three-block binary glue. -/
namespace Atlas.Rudvalis
open scoped BigOperators

abbrev FrameGlueRealCoordinate := Fin 3 × Fin 8

noncomputable def frameGlueRealMarking : FrameGlueRealCoordinate ≃ FrameGlueCoordinate where
  toFun z := (z.1,seedInnerEquiv (frameGlueRow z.1) (signedPositionIndex z.2))
  invFun z := (z.1,signedPositionIndex ((seedInnerEquiv (frameGlueRow z.1)).symm z.2))
  left_inv z := by
    simp only [Equiv.symm_apply_apply]
    have h (k : Fin 8) : signedPositionIndex (signedPositionIndex k)=k := by decide +kernel +revert
    rw [h]
  right_inv z := by
    have h (k : Fin 8) : signedPositionIndex (signedPositionIndex k)=k := by decide +kernel +revert
    simp only [h,Equiv.apply_symm_apply]

/-- Pullback on the three rows 1,2,4: output row 2r reads input row r. -/
def frameGlueRealT : Equiv.Perm FrameGlueRealCoordinate :=
  Equiv.prodCongr ⟨(fun i => ![2,0,1] i),(fun i => ![1,2,0] i),by decide +kernel,by decide +kernel⟩ seedTIndexEquiv

def frameGlueRealUnit (u : Fin 8) : Equiv.Perm FrameGlueRealCoordinate :=
  Equiv.prodCongr (Equiv.refl _) ⟨seedUnitSource u,seedUnitSource u,seedUnit_source_involution u,seedUnit_source_involution u⟩

theorem frameGlueRealT_actual (z : FrameGlueRealCoordinate) :
    seedTCoord (frameGlueRow z.1,z.2)=
      (frameGlueRow (frameGlueRealT z).1,(frameGlueRealT z).2) := by
  decide +kernel +revert

def frameGlueRealOrbitPerm (o : Fin 24) : Equiv.Perm FrameGlueRealCoordinate :=
  (frameGlueRealT^(o.val/8)).trans (frameGlueRealUnit ⟨o.val%8,Nat.mod_lt _ (by decide)⟩)

noncomputable def frameGlueOrbitPerm (o : Fin 24) : Equiv.Perm FrameGlueCoordinate :=
  (frameGlueRealMarking.symm.trans (frameGlueRealOrbitPerm o)).trans frameGlueRealMarking

noncomputable def frameGlueOrbitWord (o : Fin 24) : FrameGlueWord := frameGlueHexad ∘ frameGlueOrbitPerm o

theorem frameGlueOrbitWord_marking (o : Fin 24) (z : FrameGlueRealCoordinate) :
    frameGlueOrbitWord o (frameGlueRealMarking z)=
      if (frameGlueRealOrbitPerm o z).2=(![5,1,3] (frameGlueRealOrbitPerm o z).1) ∨
         (frameGlueRealOrbitPerm o z).2=(![6,3,5] (frameGlueRealOrbitPerm o z).1) then 1 else 0 := by
  change frameGlueHexad (frameGlueRealMarking
    (frameGlueRealOrbitPerm o (frameGlueRealMarking.symm (frameGlueRealMarking z))))=_
  rw [Equiv.symm_apply_apply]
  exact frameGlueHexad_real_positions _ _

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem frameGlueOrbit_generator_pairing (o : Fin 24) (j : FrameGlueGeneratorIndex) :
    Atlas.Codes.binaryDot (frameGlueNormalMap (frameGlueParameterGenerator j)) (frameGlueOrbitWord o)=0 := by
  rw [Atlas.Codes.binaryDot_apply,← Equiv.sum_comp frameGlueRealMarking]
  simp_rw [frameGlueOrbitWord_marking]
  decide +kernel +revert

theorem frameGlueOrbitWord_mem (o : Fin 24) : frameGlueOrbitWord o∈frameGlueCode := by
  rw [← frameGlueCode_self_dual]
  rintro w ⟨a,rfl⟩
  rw [← frameGlueParameter_expansion a]
  simp [map_sum,map_smul,frameGlueOrbit_generator_pairing]

def frameGlueOrbitBasisIndex (i : Fin 12) : Fin 24 := ![0,1,2,3,4,5,6,8,9,10,12,16] i

def frameGlueOrbitPivot (i : Fin 12) : FrameGlueRealCoordinate :=
  (⟨(![5,4,1,0,8,16,12,6,2,9,10,3] i : Fin 24).val/8,by omega⟩,
   ⟨(![5,4,1,0,8,16,12,6,2,9,10,3] i : Fin 24).val%8,Nat.mod_lt _ (by decide)⟩)

noncomputable def frameGlueOrbitMatrix : Matrix (Fin 12) (Fin 12) Bit :=
  fun i j => frameGlueOrbitWord (frameGlueOrbitBasisIndex j) (frameGlueRealMarking (frameGlueOrbitPivot i))


def frameGlueOrbitInverse : Matrix (Fin 12) (Fin 12) Bit :=
  ![![0,1,0,0,1,1,1,0,0,1,0,0],
    ![0,0,0,0,0,1,1,1,0,1,0,0],
    ![0,0,0,0,0,0,0,0,1,0,0,0],
    ![0,1,0,1,1,0,1,1,0,1,0,0],
    ![1,1,0,0,1,1,1,0,0,1,1,0],
    ![1,1,0,0,0,1,1,0,0,1,1,0],
    ![0,1,0,0,1,0,1,1,0,1,0,0],
    ![0,0,0,0,1,0,0,0,0,0,1,0],
    ![0,1,0,1,1,0,0,1,0,1,0,1],
    ![0,1,0,0,1,0,0,1,0,1,0,0],
    ![1,0,0,0,1,0,0,1,0,0,1,0],
    ![0,0,1,1,0,0,0,0,1,0,0,1]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem frameGlueOrbitInverse_mul : frameGlueOrbitInverse*frameGlueOrbitMatrix=1 := by
  ext i j
  change (∑ k : Fin 12,frameGlueOrbitInverse i k *
    frameGlueOrbitWord (frameGlueOrbitBasisIndex j) (frameGlueRealMarking (frameGlueOrbitPivot k)))=
      (1 : Matrix (Fin 12) (Fin 12) Bit) i j
  simp_rw [frameGlueOrbitWord_marking]
  simp only [Matrix.one_apply]
  decide +kernel +revert

noncomputable def frameGlueOrbitLinearMap : (Fin 12 → Bit) →ₗ[Bit] FrameGlueWord where
  toFun c := ∑ j : Fin 12,c j • frameGlueOrbitWord (frameGlueOrbitBasisIndex j)
  map_add' c d := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum,smul_smul]

theorem frameGlueOrbitLinearMap_injective : Function.Injective frameGlueOrbitLinearMap := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro c hc
  have hm : frameGlueOrbitMatrix.mulVec c=0 := by
    ext i
    have h := congrFun hc (frameGlueRealMarking (frameGlueOrbitPivot i))
    change (∑ j : Fin 12,frameGlueOrbitMatrix i j*c j)=0
    simpa [frameGlueOrbitMatrix,frameGlueOrbitLinearMap,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm] using h
  have h := congrArg (Matrix.mulVec frameGlueOrbitInverse) hm
  rw [Matrix.mulVec_mulVec,frameGlueOrbitInverse_mul,Matrix.one_mulVec,Matrix.mulVec_zero] at h
  exact h

theorem frameGlueOrbitLinearMap_range : frameGlueOrbitLinearMap.range=frameGlueCode := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro w ⟨c,rfl⟩
    change (∑ j : Fin 12,c j • frameGlueOrbitWord (frameGlueOrbitBasisIndex j))∈frameGlueCode
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (frameGlueOrbitWord_mem (frameGlueOrbitBasisIndex j)))
  · rw [LinearMap.finrank_range_of_inj frameGlueOrbitLinearMap_injective,frameGlueCode_finrank]
    simp

/-- A small linear certificate: 12 independent members of the literal 24-element orbit. -/
theorem frameGlueHexad_orbit_spans :
    Submodule.span Bit (Set.range frameGlueOrbitWord)=frameGlueCode := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨o,rfl⟩
    exact frameGlueOrbitWord_mem o
  · rw [← frameGlueOrbitLinearMap_range]
    rintro w ⟨c,rfl⟩
    change (∑ j : Fin 12,c j • frameGlueOrbitWord (frameGlueOrbitBasisIndex j))∈_
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨frameGlueOrbitBasisIndex j,rfl⟩

end Atlas.Rudvalis
