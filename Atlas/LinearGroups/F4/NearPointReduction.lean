import Atlas.LinearGroups.F4.NearSpinReduction
import Atlas.LinearGroups.F4.ShortRadicalLayer

/-! Actual Levi Weyl pivots and radical removal for the near-point chart. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

def nearPivotWord : Fin 8→List (Fin 5) :=
  ![[],[2,3],[1,3],[1,2],[3],[2],[1],[1,2,3]]

def nearDualCoordinate : Fin 8→Fin 27 := ![10,9,8,7,18,17,16,14]

theorem nearPivot_dual_destination : ∀ i : Fin 8,
    longRootWordDestination (nearPivotWord i) (nearDualCoordinate i)=10 := by
  decide +kernel

private theorem nearWeyl_mem (k : Fin 3) :
    longRootStepElement (F:=F) (![1,2,3] k)∈parabolicPointStabilizer := by
  have h (j : Fin 6) : shortRootFirstPair (leviShortIndex j) (1:F)∈parabolicPointStabilizer := by
    simpa only [leviShortRoot,shortRoot,Fin.val_zero,pow_zero,one_mul,inv_one,mul_one] using
      (leviShortRoot (F:=F) j 1).prop
  fin_cases k
  · exact (parabolicPointStabilizer (F:=F)).mul_mem
      ((parabolicPointStabilizer (F:=F)).mul_mem (h 0) (h 5)) (h 0)
  · exact (parabolicPointStabilizer (F:=F)).mul_mem
      ((parabolicPointStabilizer (F:=F)).mul_mem (h 1) (h 4)) (h 1)
  · exact (parabolicPointStabilizer (F:=F)).mul_mem
      ((parabolicPointStabilizer (F:=F)).mul_mem (h 2) (h 3)) (h 2)

-- Verified Weyl elements remain opaque during subgroup word membership.
attribute [local irreducible] longRootStepElement

def nearPivot (i : Fin 8) : parabolicPointStabilizer (F:=F) :=
  ⟨longRootWordElement (nearPivotWord i),by
    have h1 := nearWeyl_mem (F:=F) 0
    have h2 := nearWeyl_mem (F:=F) 1
    have h3 := nearWeyl_mem (F:=F) 2
    fin_cases i <;>
      simp only [nearPivotWord,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Matrix.cons_val_zero',Matrix.cons_val_succ',longRootWordElement,one_mul]
    all_goals repeat first
      | exact (parabolicPointStabilizer (F:=F)).one_mem
      | exact h1 | exact h2 | exact h3
      | apply (parabolicPointStabilizer (F:=F)).mul_mem⟩

theorem nearVector_pairing_dual (c : F) (v : Fin 8→F) (i : Fin 8) :
    tracePairing (nearVector c v) (basisVector (albertCoordinateOfFin (nearDualCoordinate i)))=v i := by
  fin_cases i <;>
    rw [tracePairing_coordinates] <;>
    simp [nearVector,upperSpinEmbed,parabolicVector,nearDualCoordinate,
      albertCoordinateOfFin,albertCoordinateFinEquiv,albertCoordinateToFin,
      basisVector,Fin.sum_univ_succ]

theorem nearPivot_nonzero_coordinate (c : F) (v : Fin 8→F) (i : Fin 8) (hi : v i≠0) :
    ((nearPivot i).val.val (nearVector c v)).2 0 0≠0 := by
  intro hz
  have h := stabilizer_tracePairing (nearPivot i).val (nearVector c v)
    (basisVector (albertCoordinateOfFin (nearDualCoordinate i)))
  have he := longRootWordElement_basis (F:=F) (nearPivotWord i) (nearDualCoordinate i)
  rw [nearPivot_dual_destination] at he
  change (nearPivot i).val.val (basisVector (albertCoordinateOfFin (nearDualCoordinate i)))=_ at he
  rw [he,nearVector_pairing_dual,tracePairing_comm,tracePairing_smul_left,
    tracePairing_comm] at h
  have hc : albertCoordinateOfFin 10 = .inr (0,7) := rfl
  rw [hc,tracePairing_octonion_basis] at h
  exact hi (by simpa [hz] using h.symm)

attribute [local irreducible] nearPivot nearClearingWord

private theorem symm_mul_apply (a b : Carrier F ≃ₗ[F] Carrier F) (x : Carrier F) :
    (a*b).symm x=b.symm (a.symm x) := rfl

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
-- Only the two surviving coordinate axes are used in this radical shear.
theorem halfRoot_near_axis (t c d : F) :
    (halfRoot 3 t).val (nearVector c (Pi.single 0 d))=
      nearVector (c-t*d) (Pi.single 0 d) := by
  unfold halfRoot
  rw [shortRoot_polynomial_all]
  apply Prod.ext
  · ext i; fin_cases i <;>
      simp [nearVector,upperSpinEmbed,parabolicVector,halfRootIndex,halfRootSign,
        shortRootL,shortRootQ,shortRootPosition,cycleCoefficient,shortRootFirstCoefficient,
        shortRootQuadraticLinear,shortRootQuadraticApply,shortRootLinear,shortRootFormula,
        coordinateCycleEquiv,Atlas.Albert.coordinateCycle,SplitOctonion.mul,
        SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
        SplitOctonion.basisVector,Pi.single_apply,Matrix.vecHead,Matrix.vecTail,
        LinearEquiv.mul_apply,symm_mul_apply] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [nearVector,upperSpinEmbed,parabolicVector,halfRootIndex,halfRootSign,
        shortRootL,shortRootQ,shortRootPosition,cycleCoefficient,shortRootFirstCoefficient,
        shortRootQuadraticLinear,shortRootQuadraticApply,shortRootLinear,shortRootFormula,
        coordinateCycleEquiv,Atlas.Albert.coordinateCycle,SplitOctonion.mul,
        SplitOctonion.conjugate,SplitOctonion.trace,SplitOctonion.unit,
        SplitOctonion.basisVector,Pi.single_apply,Matrix.vecHead,Matrix.vecTail,
        LinearEquiv.mul_apply,symm_mul_apply] <;> ring

/-- Every rank-one vector in the intrinsic nine-space outside its marked line
can be carried to a nonzero scalar multiple of A₀ by the actual parabolic. -/
theorem nearVector_parabolic_reduce (c : F) (v : Fin 8→F)
    (hv : v≠0) (hq : nearQuadratic v=0) :
    ∃ (g : parabolicPointStabilizer (F:=F)) (d : F), d≠0 ∧
      g.val.val (nearVector c v)=d • baseVector := by
  have hi : ∃ i, v i≠0 := by
    by_contra hn
    push_neg at hn
    exact hv (funext hn)
  obtain ⟨i,hi⟩ := hi
  let k := nearPivot (F:=F) i
  let x := k.val.val (nearVector c v)
  have hx : x∈parabolicImageZero :=
    parabolicPointStabilizer_preserves_imageZero k (nearVector_mem_imageZero c v)
  let w := nearSpinCoordinates x
  have hw : w 0≠0 := nearPivot_nonzero_coordinate c v i hi
  have ha : adjoint x=0 := by
    change adjoint (k.val.val (nearVector c v))=0
    rw [stabilizer_adjoint,(nearVector_rankOne_iff c v).mpr hq,map_zero]
  have hq' : nearQuadratic w=0 := (imageZero_rankOne_iff x hx).mp ha
  let d := w 0
  let r : parabolicPointStabilizer (F:=F) :=
    ⟨halfRoot 3 (x.2 2 0/d),halfRoot_parabolic 3 _⟩
  refine ⟨r*nearClearingWord w*k,d,hw,?_⟩
  change (halfRoot 3 (x.2 2 0/d)).val ((nearClearingWord w).val.val x)=_
  have hred := nearVector_reduce_pivot (x.2 2 0) w hw hq'
  rw [nearVector_reconstruction x hx] at hred
  rw [hred,halfRoot_near_axis]
  have hc : x.2 2 0-(x.2 2 0/d)*d=0 := by field_simp [d,hw]; ring
  rw [hc]
  dsimp only [d]
  apply Prod.ext
  · ext j; fin_cases j <;> simp [nearVector,upperSpinEmbed,parabolicVector,baseVector]
  · ext j l; fin_cases j <;> fin_cases l <;>
      simp [nearVector,upperSpinEmbed,parabolicVector,baseVector,SplitOctonion.basisVector,Pi.single_apply]

end Atlas.F4
