import Atlas.LinearGroups.ReeF4.WeylCoordinateTransport
import Atlas.LinearGroups.ReeF4.SpecialTerminalPivot
import Atlas.LinearGroups.ReeF4.RootGroupMembership

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert

section Ring
variable {F : Type*} [CommRing F] [CharP F 2]
set_option maxHeartbeats 1200000 in
/-- The final negative natural block needs no A−4=0 assumption. -/
theorem negativeC3_raw_identity (x y : Fin 26 → F)
    (hz : ∀ j, j≠2 → j≠18 → j≠19 → x j=0) :
    x 18*x 19*isotropyRawStar x y 19 =
      x 19^2*isotropyRawStar x y 10 + x 2*x 19*isotropyCross x y 11 +
      x 2^2*isotropyRawStar x y 13 := by
  have hz0 : x 0=0 := hz 0 (by decide) (by decide) (by decide)
  have hz1 : x 1=0 := hz 1 (by decide) (by decide) (by decide)
  have hz3 : x 3=0 := hz 3 (by decide) (by decide) (by decide)
  have hz4 : x 4=0 := hz 4 (by decide) (by decide) (by decide)
  have hz5 : x 5=0 := hz 5 (by decide) (by decide) (by decide)
  have hz6 : x 6=0 := hz 6 (by decide) (by decide) (by decide)
  have hz7 : x 7=0 := hz 7 (by decide) (by decide) (by decide)
  have hz8 : x 8=0 := hz 8 (by decide) (by decide) (by decide)
  have hz9 : x 9=0 := hz 9 (by decide) (by decide) (by decide)
  have hz10 : x 10=0 := hz 10 (by decide) (by decide) (by decide)
  have hz11 : x 11=0 := hz 11 (by decide) (by decide) (by decide)
  have hz12 : x 12=0 := hz 12 (by decide) (by decide) (by decide)
  have hz13 : x 13=0 := hz 13 (by decide) (by decide) (by decide)
  have hz14 : x 14=0 := hz 14 (by decide) (by decide) (by decide)
  have hz15 : x 15=0 := hz 15 (by decide) (by decide) (by decide)
  have hz16 : x 16=0 := hz 16 (by decide) (by decide) (by decide)
  have hz17 : x 17=0 := hz 17 (by decide) (by decide) (by decide)
  have hz20 : x 20=0 := hz 20 (by decide) (by decide) (by decide)
  have hz21 : x 21=0 := hz 21 (by decide) (by decide) (by decide)
  have hz22 : x 22=0 := hz 22 (by decide) (by decide) (by decide)
  have hz23 : x 23=0 := hz 23 (by decide) (by decide) (by decide)
  have hz24 : x 24=0 := hz 24 (by decide) (by decide) (by decide)
  have hz25 : x 25=0 := hz 25 (by decide) (by decide) (by decide)
  simp only [isotropyRawStar,isotropyCross,Matrix.cons_val,hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz10,hz11,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,mul_zero,zero_mul,add_zero,zero_add]
  apply CharTwo.add_eq_zero.mp
  ring_nf
  all_goals simp [CharTwo.ofNat_eq_mod,CharTwo.two_eq_zero]
end Ring

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem IsSpecialVector.negativeC4_zero_of_reduced_negativeC3 {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) {u : TraceZero F} (hu : IsSpecialVector m u)
    (hz : ∀ j, j≠2 → j≠18 → j≠19 → isotropyCoordinates u j=0)
    (hc : isotropyCoordinates u 19≠0) : isotropyCoordinates u 18=0 := by
  obtain ⟨_,v,hd,he⟩ := hu
  have hi := negativeC3_raw_identity (isotropyCoordinates u) (isotropyCoordinates v) hz
  have hcross : isotropyCross (isotropyCoordinates u) (isotropyCoordinates v)=0 := by
    rw [←isotropyCross_actual,hd.2,_root_.map_zero]
  have h10 := hz 10 (by decide) (by decide) (by decide)
  have h13 := hz 13 (by decide) (by decide) (by decide)
  rw [fixedStar_coordinate_theta hcard u v hd he 19,
    fixedStar_coordinate_theta hcard u v hd he 10,
    fixedStar_coordinate_theta hcard u v hd he 13] at hi
  simp only [hcross,h10,h13,_root_.map_zero,Pi.zero_apply,mul_zero,add_zero] at hi
  have ht : theta F m (isotropyCoordinates u 19)≠0 := by
    intro h
    apply hc
    apply (theta F m).injective
    simpa only [_root_.map_zero] using h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right ht)).resolve_right hc

def negativeC3PivotA (u : TraceZero F) : F := u.val.2 1 1/u.val.2 2 1
def negativeC3PivotB (m : ℕ) (u : TraceZero F) : F :=
  (u.val.2 1 0+theta F m (negativeC3PivotA u)*u.val.2 1 1)/u.val.2 2 1

def negativeC3Pivot {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (u : TraceZero F) : Model F m :=
  ⟨shortRootPairEquiv m hcard (negativeC3PivotA u) (negativeC3PivotB m u),
    shortRootPairEquiv_mem_modelSubgroup hcard _ _⟩

theorem negativeC3Pivot_Bm3_zero {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) (hc : u.val.2 2 1≠0) :
    ((negativeC3Pivot hcard u).val u).val.2 1 1=0 := by
  change u.val.2 1 1+(u.val.2 1 1/u.val.2 2 1)*u.val.2 2 1=0
  rw [div_mul_cancel₀ _ hc,CharTwo.add_self_eq_zero]

theorem negativeC3Pivot_Bm4_zero {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) (hc : u.val.2 2 1≠0) :
    ((negativeC3Pivot hcard u).val u).val.2 1 0=0 := by
  change (u.val.2 1 0+negativeC3PivotB m u*u.val.2 2 1)+
    theta F m (negativeC3PivotA u)*u.val.2 1 1=0
  rw [negativeC3PivotB,div_mul_cancel₀ _ hc]
  linear_combination (u.val.2 1 0+theta F m (negativeC3PivotA u)*u.val.2 1 1)*
    (CharTwo.two_eq_zero (R := F))

/-- The short-root pivot preserves this final five-dimensional filtration
piece and kills its two intervening B coordinates. -/
theorem negativeC3Pivot_support {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F)
    (hz : ∀ j, specialAbsoluteGrade 19 < specialAbsoluteGrade j → isotropyCoordinates u j=0)
    (hc : u.val.2 2 1≠0) :
    ∀ j, j≠2 → j≠18 → j≠19 → isotropyCoordinates ((negativeC3Pivot hcard u).val u) j=0 := by
  have hz0 : u.val.1 1=0 := hz 0 (by decide)
  have hz1 : u.val.1 0=0 := hz 1 (by decide)
  have hz3 : u.val.2 0 1=0 := hz 3 (by decide)
  have hz4 : u.val.2 0 2=0 := hz 4 (by decide)
  have hz5 : u.val.2 0 3=0 := hz 5 (by decide)
  have hz6 : u.val.2 0 4=0 := hz 6 (by decide)
  have hz7 : u.val.2 0 5=0 := hz 7 (by decide)
  have hz8 : u.val.2 0 6=0 := hz 8 (by decide)
  have hz9 : u.val.2 0 7=0 := hz 9 (by decide)
  have hz12 : u.val.2 1 2=0 := hz 12 (by decide)
  have hz13 : u.val.2 1 3=0 := hz 13 (by decide)
  have hz14 : u.val.2 1 4=0 := hz 14 (by decide)
  have hz15 : u.val.2 1 5=0 := hz 15 (by decide)
  have hz16 : u.val.2 1 6=0 := hz 16 (by decide)
  have hz17 : u.val.2 1 7=0 := hz 17 (by decide)
  have hz20 : u.val.2 2 2=0 := hz 20 (by decide)
  have hz21 : u.val.2 2 3=0 := hz 21 (by decide)
  have hz22 : u.val.2 2 4=0 := hz 22 (by decide)
  have hz23 : u.val.2 2 5=0 := hz 23 (by decide)
  have hz24 : u.val.2 2 6=0 := hz 24 (by decide)
  have hz25 : u.val.2 2 7=0 := hz 25 (by decide)
  have ht := u.property
  change u.val.1 0+u.val.1 1+u.val.1 2=0 at ht
  simp only [hz0,hz1,zero_add] at ht
  intro j h2 h18 h19
  fin_cases j
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · exact False.elim (h2 rfl)
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · exact negativeC3Pivot_Bm4_zero hcard u hc
  · exact negativeC3Pivot_Bm3_zero hcard u hc
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · exact False.elim (h18 rfl)
  · exact False.elim (h19 rfl)
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]
  · change _=0
    simp [negativeC3Pivot,isotropyCoordinates,shortRootPairEquiv_apply,shortRootPairLinear,
      shortRootParameterLinear,shortRootCenterLinear,shortRootParameterFormula,shortRootCenterFormula,
      hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz12,hz13,hz14,hz15,hz16,hz17,hz20,hz21,hz22,hz23,hz24,hz25,ht]

def negativeC3PivotDescent {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (u : TraceZero F) : Model F m :=
  ⟨weylRho,weylOperator_mem_modelSubgroup m 0⟩ * negativeC3Pivot hcard u

private theorem negativeC3_sparse_reconstruct (w : TraceZero F)
    (hs : ∀ j, j≠2 → j≠19 → isotropyCoordinates w j=0) :
    w=(w.val.2 0 0) • rootVector (0,0)+(w.val.2 2 1) • rootVector (2,1) := by
  have hs0 : w.val.1 1=0 := hs 0 (by decide) (by decide)
  have hs1 : w.val.1 0=0 := hs 1 (by decide) (by decide)
  have hs3 : w.val.2 0 1=0 := hs 3 (by decide) (by decide)
  have hs4 : w.val.2 0 2=0 := hs 4 (by decide) (by decide)
  have hs5 : w.val.2 0 3=0 := hs 5 (by decide) (by decide)
  have hs6 : w.val.2 0 4=0 := hs 6 (by decide) (by decide)
  have hs7 : w.val.2 0 5=0 := hs 7 (by decide) (by decide)
  have hs8 : w.val.2 0 6=0 := hs 8 (by decide) (by decide)
  have hs9 : w.val.2 0 7=0 := hs 9 (by decide) (by decide)
  have hs10 : w.val.2 1 0=0 := hs 10 (by decide) (by decide)
  have hs11 : w.val.2 1 1=0 := hs 11 (by decide) (by decide)
  have hs12 : w.val.2 1 2=0 := hs 12 (by decide) (by decide)
  have hs13 : w.val.2 1 3=0 := hs 13 (by decide) (by decide)
  have hs14 : w.val.2 1 4=0 := hs 14 (by decide) (by decide)
  have hs15 : w.val.2 1 5=0 := hs 15 (by decide) (by decide)
  have hs16 : w.val.2 1 6=0 := hs 16 (by decide) (by decide)
  have hs17 : w.val.2 1 7=0 := hs 17 (by decide) (by decide)
  have hs18 : w.val.2 2 0=0 := hs 18 (by decide) (by decide)
  have hs20 : w.val.2 2 2=0 := hs 20 (by decide) (by decide)
  have hs21 : w.val.2 2 3=0 := hs 21 (by decide) (by decide)
  have hs22 : w.val.2 2 4=0 := hs 22 (by decide) (by decide)
  have hs23 : w.val.2 2 5=0 := hs 23 (by decide) (by decide)
  have hs24 : w.val.2 2 6=0 := hs 24 (by decide) (by decide)
  have hs25 : w.val.2 2 7=0 := hs 25 (by decide) (by decide)
  have ht := w.property
  change w.val.1 0+w.val.1 1+w.val.1 2=0 at ht
  simp only [hs0,hs1,zero_add] at ht
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [rootVector,smul_eq_mul,hs0,hs1,ht]
  · funext b j
    fin_cases b <;> fin_cases j <;>
      simp [rootVector,Pi.single_apply,smul_eq_mul,hs0,hs1,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13,hs14,hs15,hs16,hs17,hs18,hs20,hs21,hs22,hs23,hs24,hs25]

private theorem negativeC3_rho_sparse (w : TraceZero F)
    (hs : ∀ j, j≠2 → j≠19 → isotropyCoordinates w j=0) :
    weylRho w=(w.val.2 0 0) • rootVector (0,0)+(w.val.2 2 1) • rootVector (2,0) := by
  have hA : weylRho (rootVector (F := F) (0,0))=rootVector (0,0) := by
    simpa [weylOperator,weylSupport,starMarkedVector,weylRootImage] using
      (weylOperator_support (F := F) 0 (.inr (0,0)))
  have hC : weylRho (rootVector (F := F) (2,1))=rootVector (2,0) := by
    simpa [weylOperator,weylSupport,starMarkedVector,weylRootImage] using
      (weylOperator_support (F := F) 0 (.inr (2,1)))
  calc
    _ = weylRho ((w.val.2 0 0) • rootVector (0,0)+(w.val.2 2 1) • rootVector (2,1)) :=
      congrArg _ (negativeC3_sparse_reconstruct w hs)
    _ = _ := by rw [_root_.map_add,weylRho.map_smul,weylRho.map_smul,hA,hC]

private theorem negativeC3_terminal_sum_support (a c : F) :
    ∀ j, specialAbsoluteGrade 18<specialAbsoluteGrade j →
      isotropyCoordinates (a • rootVector (F := F) (0,0)+c • rootVector (2,0)) j=0 := by
  intro j hj
  have hgrade : specialAbsoluteGrade 18 = -11 := by decide
  rw [hgrade] at hj
  fin_cases j <;> norm_num [specialAbsoluteGrade,Matrix.cons_val] at hj
  all_goals simp [isotropyCoordinates,rootVector,Pi.single_apply,smul_eq_mul]

theorem specialVector_negativeC3_descent {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) {u : TraceZero F} (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 19 < specialAbsoluteGrade j → isotropyCoordinates u j=0)
    (hc : u.val.2 2 1≠0) :
    let z := (negativeC3PivotDescent hcard u).val u
    IsSpecialVector m z ∧ z.val.2 2 0=u.val.2 2 1 ∧
      ∀ j, specialAbsoluteGrade 18 < specialAbsoluteGrade j → isotropyCoordinates z j=0 := by
  let w := (negativeC3Pivot hcard u).val u
  have hw : IsSpecialVector m w := hu.map_model (negativeC3Pivot hcard u)
  have hs := negativeC3Pivot_support hcard u hz hc
  have hwc : isotropyCoordinates w 19≠0 := hc
  have h18 := hw.negativeC4_zero_of_reduced_negativeC3 hcard hs hwc
  have hs' : ∀ j, j≠2 → j≠19 → isotropyCoordinates w j=0 := by
    intro j h2 h19
    by_cases he : j=18
    · simpa only [he] using h18
    · exact hs j h2 he h19
  have he := negativeC3_rho_sparse w hs'
  refine ⟨hu.map_model (negativeC3PivotDescent hcard u),?_,?_⟩
  · change (weylRho w).val.2 2 0=u.val.2 2 1
    rw [he]
    change (w.val.2 0 0)*0+(w.val.2 2 1)*1=u.val.2 2 1
    simpa only [mul_zero,mul_one,zero_add] using
      (show w.val.2 2 1=u.val.2 2 1 from rfl)
  · change ∀ j, specialAbsoluteGrade 18<specialAbsoluteGrade j → isotropyCoordinates (weylRho w) j=0
    rw [he]
    exact negativeC3_terminal_sum_support _ _

end Atlas.ReeF4
