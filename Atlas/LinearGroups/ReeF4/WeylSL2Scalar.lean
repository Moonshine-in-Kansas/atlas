import Atlas.LinearGroups.ReeF4.WeylSL2Diagonal

/-! The scalar torus centralizing the actual fundamental SL₂ representation. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

abbrev LongSL2Scalars (F : Type*) :=
  (Fin 4 → F) × (Fin 2 → F) × (Fin 2 → F) × (Fin 2 → F)

def longSL2BlockScale (s : LongSL2Scalars F) (w : LongSL2Blocks F) : LongSL2Blocks F :=
  (fun i => s.1 i • w.1 i,
   fun i => s.2.1 i • w.2.1 i,
   fun i => s.2.2.1 i • w.2.2.1 i,
   w.2.2.2.1,
   fun i => s.2.2.2 i * w.2.2.2.2 i)

theorem longSL2BlockScale_commute (s : LongSL2Scalars F) (σ : F →+* F)
    (A : LongSL2 (F := F)) (w : LongSL2Blocks F) :
    longSL2BlocksAction σ A (longSL2BlockScale s w) =
      longSL2BlockScale s (longSL2BlocksAction σ A w) := by
  apply Prod.ext
  · funext i
    exact _root_.map_smul (Matrix.SpecialLinearGroup.toLin' A) (s.1 i) (w.1 i)
  · apply Prod.ext
    · funext i
      exact _root_.map_smul
        (Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map σ A))
        (s.2.1 i) (w.2.1 i)
    · apply Prod.ext
      · funext i
        exact _root_.map_smul
          (longSL2TensorCurried A (Matrix.SpecialLinearGroup.map σ A))
          (s.2.2.1 i) (w.2.2.1 i)
      · rfl

def longSL2CentralExponent (m : ℕ) (r : ShortRootLabel) : ℤ :=
  let t : ℤ := (2^(m+1) : ℕ)
  (![![1,t-1,t-1,3-2*t,2*t-3,1-t,1-t,-1],
     ![2*t-2,2-t,2-t,0,0,t-2,t-2,2-2*t],
     ![1,t-1,t-1,2*t-3,3-2*t,1-t,1-t,-1]]) r.1 r.2

theorem torusWeight_scalar (m : ℕ) (c : Fˣ) (r : ShortRootLabel) :
    torusWeight m c c r = c ^ longSL2CentralExponent m r := by
  unfold torusWeight
  rw [← zpow_add]
  congr 1
  rcases r with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [torusWeightExponents, longSL2CentralExponent] <;> ring

def longSL2ScalarTable (m : ℕ) (c : Fˣ) : LongSL2Scalars F :=
  let t : ℤ := (2^(m+1) : ℕ)
  (fun i => ((c ^ (![-1,1,2*t-3,3-2*t] i) : Fˣ) : F),
   fun i => ((c ^ (![t-2,2-t] i) : Fˣ) : F),
   fun i => ((c ^ (![t-1,1-t] i) : Fˣ) : F),
   fun i => ((c ^ (![2*t-2,2-2*t] i) : Fˣ) : F))

set_option maxHeartbeats 800000 in
theorem torusEquiv_scalar_blocks (m : ℕ) (c : Fˣ) (w : TraceZero F) :
    longSL2BlocksEquiv (torusEquiv m c c w) =
      longSL2BlockScale (longSL2ScalarTable m c) (longSL2BlocksEquiv w) := by
  apply Prod.ext
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [longSL2BlocksEquiv, longSL2ToBlocks, torusEquiv, rootDiagonalEquiv,
        rootDiagonalLinear, rootDiagonalFormula, torusWeight_scalar,
        longSL2CentralExponent, longSL2ScalarTable, longSL2BlockScale, smul_eq_mul]
  · apply Prod.ext
    · funext i j
      fin_cases i <;> fin_cases j <;>
        simp [longSL2BlocksEquiv, longSL2ToBlocks, torusEquiv, rootDiagonalEquiv,
          rootDiagonalLinear, rootDiagonalFormula, torusWeight_scalar,
          longSL2CentralExponent, longSL2ScalarTable, longSL2BlockScale, smul_eq_mul]
    · apply Prod.ext
      · funext i j k
        fin_cases i <;> fin_cases j <;> fin_cases k <;>
          simp [longSL2BlocksEquiv, longSL2ToBlocks, torusEquiv, rootDiagonalEquiv,
            rootDiagonalLinear, rootDiagonalFormula, torusWeight_scalar,
            longSL2CentralExponent, longSL2ScalarTable, longSL2BlockScale, smul_eq_mul]
      · apply Prod.ext
        · funext i j
          fin_cases i <;> fin_cases j <;>
            simp [longSL2BlocksEquiv, longSL2ToBlocks, torusEquiv, rootDiagonalEquiv,
              rootDiagonalLinear, rootDiagonalFormula, torusWeight_scalar,
              longSL2CentralExponent, longSL2ScalarTable, longSL2BlockScale]
        · funext i
          fin_cases i <;>
            simp [longSL2BlocksEquiv, longSL2ToBlocks, torusEquiv, rootDiagonalEquiv,
              rootDiagonalLinear, rootDiagonalFormula, torusWeight_scalar,
              longSL2CentralExponent, longSL2ScalarTable, longSL2BlockScale]

theorem longSL2Representation_blocks (σ : F →+* F) (A : LongSL2 (F := F))
    (w : TraceZero F) :
    longSL2BlocksEquiv (longSL2Representation σ A w) =
      longSL2BlocksAction σ A (longSL2BlocksEquiv w) := by
  exact (longSL2BlocksEquiv (F := F)).apply_symm_apply _

theorem torusEquiv_scalar_commutes (m : ℕ) (c : Fˣ) (σ : F →+* F)
    (A : LongSL2 (F := F)) :
    Commute (torusEquiv m c c) (longSL2Representation σ A) := by
  apply LinearEquiv.ext
  intro w
  apply (longSL2BlocksEquiv (F := F)).injective
  change longSL2BlocksEquiv (torusEquiv m c c (longSL2Representation σ A w)) =
    longSL2BlocksEquiv (longSL2Representation σ A (torusEquiv m c c w))
  rw [torusEquiv_scalar_blocks, longSL2Representation_blocks,
    longSL2Representation_blocks, torusEquiv_scalar_blocks]
  exact (longSL2BlockScale_commute _ _ _ _).symm

theorem longSL2_scalar_intersection (m : ℕ) (σ : F →+* F)
    (A : LongSL2 (F := F)) (c : Fˣ)
    (h : longSL2Representation σ A = torusEquiv m c c) : A = 1 ∧ c = 1 := by
  have hv (v : Fin 2 → F) : Matrix.SpecialLinearGroup.toLin' A v = (c : F) • v := by
    let w : LongSL2Blocks F := (![0,v,0,0],0,0,0,0)
    have hw := congrArg
      (fun e : TraceZero F ≃ₗ[F] TraceZero F =>
        (longSL2BlocksEquiv (e (longSL2BlocksEquiv.symm w))).1 1) h
    rw [longSL2Representation_blocks, torusEquiv_scalar_blocks,
      LinearEquiv.apply_symm_apply] at hw
    simpa only [longSL2BlocksAction, LinearEquiv.prodCongr_apply,
      LinearEquiv.piCongrRight_apply, longSL2BlockScale, longSL2ScalarTable,
      Matrix.cons_val_one, Matrix.cons_val_zero, zpow_one, w] using hw
  have hmat : (A : Matrix (Fin 2) (Fin 2) F) = (c : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [_root_.map_smul, Matrix.toLin'_one]
    exact hv v
  have hsq : (c : F)^2 = 1 := by
    have hd := congrArg Matrix.det hmat
    simpa only [Matrix.det_smul, Fintype.card_fin, Matrix.det_one,
      mul_one, Matrix.SpecialLinearGroup.det_coe] using hd.symm
  have hcF : (c : F) = 1 := by
    apply (frobeniusEquiv F 2).injective
    change (c : F)^2 = (1 : F)^2
    simpa using hsq
  have hc : c = 1 := Units.ext hcF
  refine ⟨?_,hc⟩
  apply Subtype.ext
  simpa only [hcF, one_smul, Matrix.SpecialLinearGroup.coe_one] using hmat

end Atlas.ReeF4
