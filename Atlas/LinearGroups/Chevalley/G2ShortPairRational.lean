import Atlas.Algebra.ClassThreeExponential
import Atlas.LinearGroups.Chevalley.ConjugatedRootExponential
import Atlas.LinearGroups.Chevalley.G2PositiveOperatorPinning

/-! Source candidate: the short 120-degree pair in a saturated G2 plane.
The extra highest-root correction is retained; this is not an A2 relation. -/

noncomputable section
namespace Atlas.Chevalley
open Integral
open scoped commutatorElement
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (hdiamond : SimpleDiamondProducts P b)
  (R : Type*) [CommRing R] [Algebra ℚ R]
include hdiamond

/-- The two short roots α and α+β have three commutator factors in G2,
with literal parameters -2st,-3s²t,-3st². -/
theorem adjointX_g2_short_pair_commutator_rat
    (i j : b.support) (hne : i ≠ j)
    (hij : b.cartanMatrix i j = -1) (hji : b.cartanMatrix j i = -3) (s t : R) :
    let ni := adjointWeyl P b R i 1
    let nj := adjointWeyl P b R j 1
    ⁅adjointX P b R i s, nj * adjointX P b R i t * nj⁻¹⁆ =
      ((ni*nj) * adjointX P b R i (-2*s*t) * (ni*nj)⁻¹) *
      (ni * adjointX P b R j (-3*s^2*t) * ni⁻¹) *
      ((nj*ni) * adjointX P b R j (-3*s*t^2) * (nj*ni)⁻¹) := by
  let A := raisingOver P b R i
  let B := raisingOver P b R j
  let C := A*B-B*A
  let D := A*C-C*A
  let L := A*D-D*A
  let F := B*L-L*B
  let ni := adjointWeyl P b R i 1
  let nj := adjointWeyl P b R j 1
  obtain ⟨hAL,_,_,hCD,hCL,hDL,_,_,hCF,hDF,hLF⟩ :=
    raisingOver_g2_cross_brackets P b hdiamond R i j hne hij hji
  change C*D-D*C = -F at hCD
  obtain ⟨hnC,hnD,hnL,hnF⟩ :=
    raisingOver_g2_positive_brackets_nilpotent P b hdiamond R i j hne hij hji
  have nilD : IsNilpotent D := by
    have h : (2:ℚ) • ((1/2:ℚ) • D) = D := by module
    rw [← h]
    exact hnD.smul (2:ℚ)
  have nilL : IsNilpotent L := by
    have h : (6:ℚ) • ((1/6:ℚ) • L) = L := by module
    rw [← h]
    exact hnL.smul (6:ℚ)
  have nilF : IsNilpotent F := by
    have h : (6:ℚ) • ((1/6:ℚ) • F) = F := by module
    rw [← h]
    exact hnF.smul (6:ℚ)
  have scaled (a c : R) (U V : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :
      (a • U)*(c • V)-(c • V)*(a • U)=(a*c) • (U*V-V*U) := by
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm c a,smul_sub]
  have h1 : (s • A)*((-t) • C)-((-t) • C)*(s • A)=(-s*t) • D := by
    rw [scaled]
    congr 1
    ring
  have h2 : (s • A)*((-s*t) • D)-((-s*t) • D)*(s • A)=(-s^2*t) • L := by
    rw [scaled]
    congr 1
    ring
  have h3 : ((-t) • C)*((-s*t) • D)-((-s*t) • D)*((-t) • C)=(-s*t^2) • F := by
    rw [scaled,hCD,smul_neg,← neg_smul]
    congr 1
    ring
  have he := Atlas.Algebra.exp_classThree_commutator
    (s • A) ((-t) • C) ((-s*t) • D) ((-s^2*t) • L) ((-s*t^2) • F)
    ((raisingOver_nilpotent P b R i).smul s) (hnC.smul (-t))
    (nilD.smul (-s*t)) (nilL.smul (-s^2*t)) (nilF.smul (-s*t^2))
    h1 h2 h3 ((hAL.smul_left s).smul_right (-s^2*t))
    ((hCL.smul_left (-t)).smul_right (-s^2*t))
    ((hDL.smul_left (-s*t)).smul_right (-s^2*t))
    ((hCF.smul_left (-t)).smul_right (-s*t^2))
    ((hDF.smul_left (-s*t)).smul_right (-s*t^2))
    ((hLF.smul_left (-s^2*t)).smul_right (-s*t^2))
  obtain ⟨hZ,hW,hV,hH⟩ :=
    adjointWeyl_g2_positive_operator_pinnings P b hdiamond R i j hne hij hji
  change nj.val.val * raisingOver P b R i * (nj⁻¹).val.val = -C at hZ
  change (ni*nj).val.val * raisingOver P b R i * ((ni*nj)⁻¹).val.val = (1/2:ℚ) • D at hW
  change ni.val.val * raisingOver P b R j * (ni⁻¹).val.val = (1/6:ℚ) • L at hV
  change (nj*ni).val.val * raisingOver P b R j * ((nj*ni)⁻¹).val.val = (1/6:ℚ) • F at hH
  have hWp : (-2*s*t) • ((1/2:ℚ) • D)=(-s*t) • D := by
    rw [show -2*s*t = (-s*t)+(-s*t) by ring,
      add_smul, ← smul_add, ← add_smul,
      show (1/2:ℚ)+(1/2:ℚ)=1 by norm_num, one_smul]
  have hVp : (-3*s^2*t) • ((1/6:ℚ) • L)=(1/2:ℚ) • ((-s^2*t) • L) := by
    rw [show -3*s^2*t = (-s^2*t)+(-s^2*t)+(-s^2*t) by ring,
      add_smul, add_smul, ← smul_add, ← smul_add, ← add_smul, ← add_smul,
      show (1/6:ℚ)+(1/6:ℚ)+(1/6:ℚ)=1/2 by norm_num]
    exact smul_comm (-s^2*t) (1/2:ℚ) L
  have hHp : (-3*s*t^2) • ((1/6:ℚ) • F)=(1/2:ℚ) • ((-s*t^2) • F) := by
    rw [show -3*s*t^2 = (-s*t^2)+(-s*t^2)+(-s*t^2) by ring,
      add_smul, add_smul, ← smul_add, ← smul_add, ← add_smul, ← add_smul,
      show (1/6:ℚ)+(1/6:ℚ)+(1/6:ℚ)=1/2 by norm_num]
    exact smul_comm (-s*t^2) (1/2:ℚ) F
  apply Subtype.ext
  apply Units.ext
  change raisingExponential P b R i s *
      (nj * adjointX P b R i t * nj⁻¹).val.val * raisingExponential P b R i (-s) *
      ((nj * adjointX P b R i t * nj⁻¹)⁻¹).val.val =
    ((ni*nj) * adjointX P b R i (-2*s*t) * (ni*nj)⁻¹).val.val *
      (ni * adjointX P b R j (-3*s^2*t) * ni⁻¹).val.val *
      ((nj*ni) * adjointX P b R j (-3*s*t^2) * (nj*ni)⁻¹).val.val
  simpa only [adjoint_conjugateX_val_eq_exp,adjoint_conjugateX_inv_val_eq_exp,
    raisingExponential_eq_nilpotent_exp,hZ,hW,hV,hH,hWp,hVp,hHp,
    smul_neg,neg_smul,neg_neg,A] using he

end Atlas.Chevalley
