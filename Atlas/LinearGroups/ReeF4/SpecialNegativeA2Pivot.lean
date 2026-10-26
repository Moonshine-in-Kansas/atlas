import Atlas.LinearGroups.ReeF4.SpecialNegativeC3Pivot
import Atlas.LinearGroups.ReeF4.SpecialLeadingReductionFramework
import Atlas.LinearGroups.ReeF4.WeylSupport

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def negativeA2PivotParameter (m : ℕ) (u : TraceZero F) : F :=
  thetaInv F m (u.val.2 0 1/u.val.2 0 2)
def negativeA2Pivot {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (u : TraceZero F) : Model F m :=
  ⟨longSL2Equiv (negativeA2PivotParameter m u) (theta F m (negativeA2PivotParameter m u)),
    longSL2Parameter_mem_modelSubgroup hcard _⟩
def negativeA2PivotDescent {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) (u : TraceZero F) : Model F m :=
  ⟨weylSigma,weylOperator_mem_modelSubgroup m 1⟩ * negativeA2Pivot hcard u

theorem negativeA2Pivot_Am3_zero {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (u : TraceZero F) (ha : u.val.2 0 2≠0) :
    ((negativeA2Pivot hcard u).val u).val.2 0 1=0 := by
  change u.val.2 0 1+theta F m (thetaInv F m (u.val.2 0 1/u.val.2 0 2))*u.val.2 0 2=0
  rw [theta_thetaInv hcard,div_mul_cancel₀ _ ha,CharTwo.add_self_eq_zero]

private theorem negativeA2_sparse_reconstruct (w : TraceZero F)
    (hz : ∀ j, j∉({2,4,10,11,12,18,20} : Finset (Fin 26)) → isotropyCoordinates w j=0) :
    w=(w.val.2 0 0) • rootVector (0,0) + (w.val.2 0 2) • rootVector (0,2) + (w.val.2 1 0) • rootVector (1,0) + (w.val.2 1 1) • rootVector (1,1) + (w.val.2 1 2) • rootVector (1,2) + (w.val.2 2 0) • rootVector (2,0) + (w.val.2 2 2) • rootVector (2,2) := by
  have h0 : w.val.1 1=0 := hz 0 (by decide)
  have h1 : w.val.1 0=0 := hz 1 (by decide)
  have h3 : w.val.2 0 1=0 := hz 3 (by decide)
  have h5 : w.val.2 0 3=0 := hz 5 (by decide)
  have h6 : w.val.2 0 4=0 := hz 6 (by decide)
  have h7 : w.val.2 0 5=0 := hz 7 (by decide)
  have h8 : w.val.2 0 6=0 := hz 8 (by decide)
  have h9 : w.val.2 0 7=0 := hz 9 (by decide)
  have h13 : w.val.2 1 3=0 := hz 13 (by decide)
  have h14 : w.val.2 1 4=0 := hz 14 (by decide)
  have h15 : w.val.2 1 5=0 := hz 15 (by decide)
  have h16 : w.val.2 1 6=0 := hz 16 (by decide)
  have h17 : w.val.2 1 7=0 := hz 17 (by decide)
  have h19 : w.val.2 2 1=0 := hz 19 (by decide)
  have h21 : w.val.2 2 3=0 := hz 21 (by decide)
  have h22 : w.val.2 2 4=0 := hz 22 (by decide)
  have h23 : w.val.2 2 5=0 := hz 23 (by decide)
  have h24 : w.val.2 2 6=0 := hz 24 (by decide)
  have h25 : w.val.2 2 7=0 := hz 25 (by decide)
  have ht := w.property
  change w.val.1 0+w.val.1 1+w.val.1 2=0 at ht
  simp only [h0,h1,zero_add] at ht
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [rootVector,smul_eq_mul,h0,h1,ht]
  · funext b j
    fin_cases b <;> fin_cases j <;>
      simp [rootVector,Pi.single_apply,smul_eq_mul,h0,h1,h3,h5,h6,h7,h8,h9,h13,h14,h15,h16,h17,h19,h21,h22,h23,h24,h25]

private theorem negativeA2_sigma_sparse (w : TraceZero F)
    (hz : ∀ j, j∉({2,4,10,11,12,18,20} : Finset (Fin 26)) → isotropyCoordinates w j=0) :
    weylSigma w=(w.val.2 0 0) • rootVector (2,0) + (w.val.2 0 2) • rootVector (2,1) + (w.val.2 1 0) • rootVector (1,0) + (w.val.2 1 1) • rootVector (1,2) + (w.val.2 1 2) • rootVector (1,1) + (w.val.2 2 0) • rootVector (0,0) + (w.val.2 2 2) • rootVector (0,1) := by
  have hs2 : weylSigma (rootVector (F := F) (0,0))=rootVector (2,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (0,0)))
  have hs4 : weylSigma (rootVector (F := F) (0,2))=rootVector (2,1) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (0,2)))
  have hs10 : weylSigma (rootVector (F := F) (1,0))=rootVector (1,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (1,0)))
  have hs11 : weylSigma (rootVector (F := F) (1,1))=rootVector (1,2) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (1,1)))
  have hs12 : weylSigma (rootVector (F := F) (1,2))=rootVector (1,1) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (1,2)))
  have hs18 : weylSigma (rootVector (F := F) (2,0))=rootVector (0,0) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (2,0)))
  have hs20 : weylSigma (rootVector (F := F) (2,2))=rootVector (0,1) := by
    simpa [weylSupport,starMarkedVector,weylRootImage,weylOperator] using
      (weylOperator_support (F := F) 1 (.inr (2,2)))
  calc
    _ = weylSigma ((w.val.2 0 0) • rootVector (0,0) + (w.val.2 0 2) • rootVector (0,2) + (w.val.2 1 0) • rootVector (1,0) + (w.val.2 1 1) • rootVector (1,1) + (w.val.2 1 2) • rootVector (1,2) + (w.val.2 2 0) • rootVector (2,0) + (w.val.2 2 2) • rootVector (2,2)) := congrArg _ (negativeA2_sparse_reconstruct w hz)
    _ = _ := by simp only [_root_.map_add,weylSigma.map_smul,hs2,hs4,hs10,hs11,hs12,hs18,hs20]

private theorem negativeA2_sigma_sparse_bounds (w : TraceZero F)
    (hz : ∀ j, j∉({2,4,10,11,12,18,20} : Finset (Fin 26)) → isotropyCoordinates w j=0) :
    (weylSigma w).val.2 2 1=w.val.2 0 2 ∧
      ∀ j, allowedSpecialLeadingRoot j → specialAbsoluteGrade 19<specialAbsoluteGrade j →
        isotropyCoordinates (weylSigma w) j=0 := by
  rw [negativeA2_sigma_sparse w hz]
  constructor
  · simp [rootVector,Pi.single_apply,smul_eq_mul]
  · intro j hj hg
    have hgrade : specialAbsoluteGrade 19 = -8 := by decide
    rw [hgrade] at hg
    fin_cases j <;> norm_num [allowedSpecialLeadingRoot,Fin.ext_iff] at hj
    all_goals norm_num [specialAbsoluteGrade,Matrix.cons_val] at hg
    all_goals simp [isotropyCoordinates,rootVector,Pi.single_apply,smul_eq_mul]

/-- Negative A2 descends to negative C3. Two intervening forbidden leading
coordinates are eliminated by the independently derived classification. -/
theorem specialVector_negativeA2_descent {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) {u : TraceZero F} (hu : IsSpecialVector m u)
    (hz : ∀ j, specialAbsoluteGrade 4 < specialAbsoluteGrade j → isotropyCoordinates u j=0)
    (ha : u.val.2 0 2≠0) :
    let z := (negativeA2PivotDescent hcard u).val u
    IsSpecialVector m z ∧ z.val.2 2 1=u.val.2 0 2 ∧
      ∀ j, specialAbsoluteGrade 19 < specialAbsoluteGrade j → isotropyCoordinates z j=0 := by
  let w := (negativeA2Pivot hcard u).val u
  have hw : IsSpecialVector m w := hu.map_model (negativeA2Pivot hcard u)
  have hz0 : u.val.1 1=0 := hz 0 (by decide)
  have hz1 : u.val.1 0=0 := hz 1 (by decide)
  have hz5 : u.val.2 0 3=0 := hz 5 (by decide)
  have hz6 : u.val.2 0 4=0 := hz 6 (by decide)
  have hz7 : u.val.2 0 5=0 := hz 7 (by decide)
  have hz8 : u.val.2 0 6=0 := hz 8 (by decide)
  have hz9 : u.val.2 0 7=0 := hz 9 (by decide)
  have hz13 : u.val.2 1 3=0 := hz 13 (by decide)
  have hz14 : u.val.2 1 4=0 := hz 14 (by decide)
  have hz15 : u.val.2 1 5=0 := hz 15 (by decide)
  have hz16 : u.val.2 1 6=0 := hz 16 (by decide)
  have hz17 : u.val.2 1 7=0 := hz 17 (by decide)
  have hz21 : u.val.2 2 3=0 := hz 21 (by decide)
  have hz22 : u.val.2 2 4=0 := hz 22 (by decide)
  have hz23 : u.val.2 2 5=0 := hz 23 (by decide)
  have hz24 : u.val.2 2 6=0 := hz 24 (by decide)
  have hz25 : u.val.2 2 7=0 := hz 25 (by decide)
  have ht := u.property
  change u.val.1 0+u.val.1 1+u.val.1 2=0 at ht
  simp only [hz0,hz1,zero_add] at ht
  have hw0 : w.val.1 1=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).1 1=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw1 : w.val.1 0=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).1 0=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw5 : w.val.2 0 3=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 0 3=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw6 : w.val.2 0 4=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 0 4=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw7 : w.val.2 0 5=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 0 5=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw8 : w.val.2 0 6=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 0 6=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw9 : w.val.2 0 7=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 0 7=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw13 : w.val.2 1 3=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 1 3=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw14 : w.val.2 1 4=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 1 4=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw15 : w.val.2 1 5=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 1 5=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw16 : w.val.2 1 6=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 1 6=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw17 : w.val.2 1 7=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 1 7=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw21 : w.val.2 2 3=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 2 3=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw22 : w.val.2 2 4=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 2 4=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw23 : w.val.2 2 5=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 2 5=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw24 : w.val.2 2 6=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 2 6=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw25 : w.val.2 2 7=0 := by
    change (longSL2Formula (negativeA2PivotParameter m u)
      (theta F m (negativeA2PivotParameter m u)) u.val).2 2 7=0
    simp only [longSL2Formula,Matrix.cons_val,hz0,hz1,hz5,hz6,hz7,hz8,hz9,hz13,hz14,hz15,hz16,hz17,hz21,hz22,hz23,hz24,hz25,ht,mul_zero,zero_mul,add_zero,zero_add]
  have hw3 : w.val.2 0 1=0 := negativeA2Pivot_Am3_zero hcard u ha
  have hw19 : w.val.2 2 1=0 := by
    have h : fullAdjointRoot10 (isotropyCoordinates w)=0 := by
      rw [←fullAdjointRoot10_actual,hw.adjoint_zero]; rfl
    change w.val.1 1*w.val.2 1 0+w.val.2 0 0*w.val.2 2 3+
      w.val.2 0 1*w.val.2 2 2+w.val.2 0 2*w.val.2 2 1+
      w.val.2 0 4*w.val.2 2 0=0 at h
    simp only [hw0,hw21,hw3,hw6,mul_zero,zero_mul,zero_add,add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left ha
  have hwsparse : ∀ j, j∉({2,4,10,11,12,18,20} : Finset (Fin 26)) → isotropyCoordinates w j=0 := by
    intro j hj
    fin_cases j
    · exact hw0
    · exact hw1
    · exact False.elim (hj (by decide))
    · exact hw3
    · exact False.elim (hj (by decide))
    · exact hw5
    · exact hw6
    · exact hw7
    · exact hw8
    · exact hw9
    · exact False.elim (hj (by decide))
    · exact False.elim (hj (by decide))
    · exact False.elim (hj (by decide))
    · exact hw13
    · exact hw14
    · exact hw15
    · exact hw16
    · exact hw17
    · exact False.elim (hj (by decide))
    · exact hw19
    · exact False.elim (hj (by decide))
    · exact hw21
    · exact hw22
    · exact hw23
    · exact hw24
    · exact hw25
  obtain ⟨he,hbounds⟩ := negativeA2_sigma_sparse_bounds w hwsparse
  have hs : IsSpecialVector m (weylSigma w) := hw.map_model
    (⟨weylSigma,weylOperator_mem_modelSubgroup m 1⟩ : Model F m)
  change IsSpecialVector m (weylSigma w) ∧
    (weylSigma w).val.2 2 1=u.val.2 0 2 ∧
    ∀ j, specialAbsoluteGrade 19<specialAbsoluteGrade j → isotropyCoordinates (weylSigma w) j=0
  exact ⟨hs,he.trans (show w.val.2 0 2=u.val.2 0 2 from rfl),
    hs.support_bound_of_allowed hcard 19 hbounds⟩
end Atlas.ReeF4
