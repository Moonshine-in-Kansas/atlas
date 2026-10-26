import Atlas.LinearGroups.ReeF4.WeylSupport
import Atlas.LinearGroups.ReeF4.SpecialLeadingExistence
import Atlas.LinearGroups.ReeF4.WeylSL2Membership
import Atlas.LinearGroups.ReeF4.WeylModel

noncomputable section
set_option maxRecDepth 8192
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

set_option maxHeartbeats 1200000 in
/-- On the last two weight spaces, the actual long-root shear followed by sigma. -/
theorem terminalPivotRaw_action (a c t z : F) :
    ((weylSigma : TraceZero F ≃ₗ[F] TraceZero F) * longSL2Equiv t z)
      (a • rootVector (0,0) + c • rootVector (2,0)) =
      c • rootVector (0,0) + (a+t*c) • rootVector (2,0) := by
  have hA : longSL2Equiv t z (rootVector (F := F) (0,0))=rootVector (0,0) := by
    apply Subtype.ext
    change longSL2Formula t z (rootVector (F := F) (0,0)).val=(rootVector (F := F) (0,0)).val
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [longSL2Formula,rootVector,Pi.single_apply]
    · funext b j
      fin_cases b <;> fin_cases j <;> simp [longSL2Formula,rootVector,Pi.single_apply]
  have hC : longSL2Equiv t z (rootVector (F := F) (2,0))=
      t • rootVector (0,0)+rootVector (2,0) := by
    apply Subtype.ext
    change longSL2Formula t z (rootVector (F := F) (2,0)).val=
      (t • rootVector (F := F) (0,0)+rootVector (2,0)).val
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [longSL2Formula,rootVector,Pi.single_apply,smul_eq_mul]
    · funext b j
      fin_cases b <;> fin_cases j <;> simp [longSL2Formula,rootVector,Pi.single_apply,smul_eq_mul]
  have hsA : weylSigma (rootVector (F := F) (0,0))=rootVector (2,0) := by
    simpa [weylOperator,weylSupport,starMarkedVector,weylRootImage] using
      (weylOperator_support (F := F) 1 (.inr (0,0)))
  have hsC : weylSigma (rootVector (F := F) (2,0))=rootVector (0,0) := by
    simpa [weylOperator,weylSupport,starMarkedVector,weylRootImage] using
      (weylOperator_support (F := F) 1 (.inr (2,0)))
  change weylSigma (longSL2Equiv t z (_+_))=_
  rw [_root_.map_add,(longSL2Equiv t z).map_smul,(longSL2Equiv t z).map_smul,hA,hC,
    _root_.map_add,weylSigma.map_smul,weylSigma.map_smul,_root_.map_add,
    weylSigma.map_smul,hsA,hsC]
  rw [smul_add,smul_smul,mul_comm c t,add_smul]
  abel

def terminalPivot {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) (a c : F) : Model F m :=
  ⟨weylSigma * longSL2Equiv (a/c) (theta F m (a/c)),
    (modelSubgroup F m).mul_mem (weylOperator_mem_modelSubgroup m 1)
      (longSL2Parameter_mem_modelSubgroup hcard _)⟩

theorem terminalPivot_action {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (a c : F) (hc : c≠0) :
    (terminalPivot hcard a c).val (a • rootVector (0,0) + c • rootVector (2,0)) =
      c • rootVector (0,0) := by
  change ((weylSigma : TraceZero F ≃ₗ[F] TraceZero F) * longSL2Equiv (a/c) (theta F m (a/c))) _ = _
  rw [terminalPivotRaw_action,div_mul_cancel₀ _ hc,CharTwo.add_self_eq_zero,
    zero_smul,add_zero]

/-- The negative C4 grade has only two remaining marked coefficients. -/
theorem terminal_support {u : TraceZero F}
    (hz : ∀ j, specialAbsoluteGrade 18 < specialAbsoluteGrade j → isotropyCoordinates u j=0) :
    u = (u.val.2 0 0) • rootVector (0,0) + (u.val.2 2 0) • rootVector (2,0) := by
  have hz0 : u.val.1 1=0 := hz 0 (by decide)
  have hz1 : u.val.1 0=0 := hz 1 (by decide)
  have hz3 : u.val.2 0 1=0 := hz 3 (by decide)
  have hz4 : u.val.2 0 2=0 := hz 4 (by decide)
  have hz5 : u.val.2 0 3=0 := hz 5 (by decide)
  have hz6 : u.val.2 0 4=0 := hz 6 (by decide)
  have hz7 : u.val.2 0 5=0 := hz 7 (by decide)
  have hz8 : u.val.2 0 6=0 := hz 8 (by decide)
  have hz9 : u.val.2 0 7=0 := hz 9 (by decide)
  have hz10 : u.val.2 1 0=0 := hz 10 (by decide)
  have hz11 : u.val.2 1 1=0 := hz 11 (by decide)
  have hz12 : u.val.2 1 2=0 := hz 12 (by decide)
  have hz13 : u.val.2 1 3=0 := hz 13 (by decide)
  have hz14 : u.val.2 1 4=0 := hz 14 (by decide)
  have hz15 : u.val.2 1 5=0 := hz 15 (by decide)
  have hz16 : u.val.2 1 6=0 := hz 16 (by decide)
  have hz17 : u.val.2 1 7=0 := hz 17 (by decide)
  have hz19 : u.val.2 2 1=0 := hz 19 (by decide)
  have hz20 : u.val.2 2 2=0 := hz 20 (by decide)
  have hz21 : u.val.2 2 3=0 := hz 21 (by decide)
  have hz22 : u.val.2 2 4=0 := hz 22 (by decide)
  have hz23 : u.val.2 2 5=0 := hz 23 (by decide)
  have hz24 : u.val.2 2 6=0 := hz 24 (by decide)
  have hz25 : u.val.2 2 7=0 := hz 25 (by decide)
  apply Subtype.ext
  apply Prod.ext
  · funext i
    have ht := u.property
    change u.val.1 0+u.val.1 1+u.val.1 2=0 at ht
    simp only [hz0,hz1,zero_add] at ht
    fin_cases i <;> simp [rootVector,smul_eq_mul,hz0,hz1,ht]
  · funext b j
    fin_cases b <;> fin_cases j <;>
      simp [rootVector,Pi.single_apply,smul_eq_mul,hz0,hz1,hz3,hz4,hz5,hz6,hz7,hz8,hz9,hz10,hz11,hz12,hz13,hz14,hz15,hz16,hz17,hz19,hz20,hz21,hz22,hz23,hz24,hz25]

/-- The actual torus normalizes a nonzero scalar multiple of the final root. -/
def terminalScalarNormalizer {m : ℕ} (hcard : Nat.card F = 2^(2*m+1))
    (c : F) (hc : c≠0) : Model F m :=
  ⟨torusEquiv m (Units.mk0 c hc)⁻¹ 1,torusEquiv_mem_modelSubgroup hcard _ _⟩

theorem terminalScalarNormalizer_action {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (c : F) (hc : c≠0) :
    (terminalScalarNormalizer hcard c hc).val (c • rootVector (0,0)) = rootVector (0,0) := by
  change torusEquiv m (Units.mk0 c hc)⁻¹ 1 (c • rootVector (0,0)) = _
  rw [(torusEquiv m (Units.mk0 c hc)⁻¹ 1).map_smul,torusEquiv_root,smul_smul]
  simp [torusWeight,torusWeightExponents,hc]

/-- The last genuine coordinate descent, including normalization in the actual model. -/
theorem specialVector_terminal_reduction {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hz : ∀ j, specialAbsoluteGrade 18 < specialAbsoluteGrade j → isotropyCoordinates u j=0)
    (hc : u.val.2 2 0≠0) :
    ∃ g : Model F m, g.val u = rootVector (0,0) := by
  refine ⟨terminalScalarNormalizer hcard (u.val.2 2 0) hc *
    terminalPivot hcard (u.val.2 0 0) (u.val.2 2 0),?_⟩
  change (terminalScalarNormalizer hcard (u.val.2 2 0) hc).val
    ((terminalPivot hcard (u.val.2 0 0) (u.val.2 2 0)).val u) = _
  have hp : (terminalPivot hcard (u.val.2 0 0) (u.val.2 2 0)).val u =
      (u.val.2 2 0) • rootVector (0,0) := by
    calc
      _ = (terminalPivot hcard (u.val.2 0 0) (u.val.2 2 0)).val
        ((u.val.2 0 0) • rootVector (0,0) + (u.val.2 2 0) • rootVector (2,0)) :=
          congrArg _ (terminal_support hz)
      _ = _ := terminalPivot_action hcard _ _ hc
  rw [hp,terminalScalarNormalizer_action]
end Atlas.ReeF4
