import Atlas.Rudvalis.FanoLinear
import Atlas.Rudvalis.BlockAffine
import Mathlib.LinearAlgebra.Basis.Bilinear

/-! Structural lifting of the Fano-plane action through changes of affine origins. -/
namespace Atlas.Rudvalis
open scoped BigOperators

theorem polar_matrix_determinant (M : BinaryMatrix) (c x y : E) :
    polar (matrixAt M c) (matrixAt M x) (matrixAt M y) = M.det * polar c x y := by
  simp [matrixAt,polar,Matrix.det_fin_three,Fin.sum_univ_succ]
  ring_nf
  have htwo : (2 : Bit)=0 := by decide
  have hneg : ∀ a : Bit, -a=a := by decide
  have hsix : (6 : Bit)=0 := by decide
  simp [htwo,hsix,sub_eq_add_neg,hneg]

theorem linearEquiv_preserves_polar (A : E ≃ₗ[Bit] E) (c x y : E) :
    polar (A c) (A x) (A y)=polar c x y := by
  let M : BinaryMatrix := LinearMap.toMatrix' A.toLinearMap
  have hm (z : E) : matrixAt M z=A z := LinearMap.toMatrix'_mulVec _ _
  have hi : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp (by
    change Function.Injective (matrixAt M)
    intro x y hxy
    apply A.injective
    simpa only [hm] using hxy)
  have hd : M.det=1 := by
    have hn := ((Matrix.isUnit_iff_isUnit_det M).mp hi).ne_zero
    rcases Atlas.Codes.bit_cases M.det with h | h
    · exact (hn h).elim
    · exact h
  simpa only [hm,hd,one_mul] using polar_matrix_determinant M c x y

noncomputable def polarBilinear (t : E) : E →ₗ[Bit] E →ₗ[Bit] Bit where
  toFun c :=
    { toFun := fun x => polar c t x
      map_add' := by intros; simp [polar]; ring
      map_smul' := by intros; simp [polar]; ring }
  map_add' := by intros; ext x; simp [polar]; ring
  map_smul' := by intros; ext x; simp [polar]; ring

theorem basisFun_eq_basisPoint (i : Fin 3) : (Pi.basisFun Bit (Fin 3)) i=(basisPoint i).val := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [Pi.basisFun_apply,basisPoint,binaryLabel]

theorem alternating_form_polar (B : E →ₗ[Bit] E →ₗ[Bit] Bit)
    (hB : ∀ c : E, B c c=0) : ∃ t : E, ∀ c x : E, B c x=polar c t x := by
  have hs (x y : E) : B x y=B y x := by
    have he := hB (x+y)
    simp only [map_add,LinearMap.add_apply,hB,zero_add,add_zero] at he
    have hcancel : ∀ a b : Bit, a+b=0 → a=b := by decide
    exact (hcancel _ _ he).symm
  let t : E := ![B (basisPoint 1).val (basisPoint 2).val,
    B (basisPoint 0).val (basisPoint 2).val,B (basisPoint 0).val (basisPoint 1).val]
  have he : B=polarBilinear t := by
    apply LinearMap.ext_basis (Pi.basisFun Bit (Fin 3)) (Pi.basisFun Bit (Fin 3))
    intro i j
    rw [basisFun_eq_basisPoint,basisFun_eq_basisPoint]
    fin_cases i <;> fin_cases j <;>
      simp [polarBilinear,polar,t,basisPoint,binaryLabel,hB,hs]
  exact ⟨t,fun c x => congrArg (fun L : E →ₗ[Bit] E →ₗ[Bit] Bit => L c x) he⟩


noncomputable def linearPointEquiv (A : E ≃ₗ[Bit] E) : Equiv.Perm Point where
  toFun p := ⟨A p.val,fun h => p.prop (A.injective (h.trans (map_zero A).symm))⟩
  invFun p := ⟨A.symm p.val,fun h => p.prop (A.symm.injective (h.trans (map_zero A.symm).symm))⟩
  left_inv p := Subtype.ext (A.symm_apply_apply p.val)
  right_inv p := Subtype.ext (A.apply_symm_apply p.val)

theorem theta_zero_parameter (p : Point) (x : E) : theta p 0 x=0 := by
  simp [theta,quadratic,eta,dot]

noncomputable def sectionDifference (A : E ≃ₗ[Bit] E) (p : Point) :
    E →ₗ[Bit] E →ₗ[Bit] Bit where
  toFun c :=
    { toFun := fun x => theta (linearPointEquiv A p) (A c) (A x)+theta p c x
      map_add' := by
        intro x y
        have h1 := theta_polarization (linearPointEquiv A p) (A c) (A x) (A y)
        rw [← map_add,linearEquiv_preserves_polar] at h1
        have h2 := theta_polarization p c x y
        have hcancel : ∀ a b c d e f r : Bit,
            a+b+c=r → d+e+f=r → a+d=(b+e)+(c+f) := by decide
        exact hcancel _ _ _ _ _ _ _ h1 h2
      map_smul' := by
        intro a x
        rcases Atlas.Codes.bit_cases a with ha | ha <;> simp [ha,theta_zero] }
  map_add' := by
    intro c d
    apply LinearMap.ext
    intro x
    change theta (linearPointEquiv A p) (A (c+d)) (A x)+theta p (c+d) x =
      (theta (linearPointEquiv A p) (A c) (A x)+theta p c x)+
      (theta (linearPointEquiv A p) (A d) (A x)+theta p d x)
    simp only [map_add,theta_add_parameter]
    ring
  map_smul' := by
    intro a c
    apply LinearMap.ext
    intro x
    rcases Atlas.Codes.bit_cases a with ha | ha <;>
      simp [ha,theta_zero_parameter]

theorem sectionDifference_diagonal (A : E ≃ₗ[Bit] E) (p : Point) (c : E) :
    sectionDifference A p c c=0 := by
  change theta (linearPointEquiv A p) (A c) (A c)+theta p c c=0
  rw [theta_normalization,theta_normalization]
  have he : (linearPointEquiv A p).val=A c ↔ p.val=c := A.injective.eq_iff
  simp only [he]
  exact Atlas.Codes.bit_self_add _

theorem section_difference_origin (A : E ≃ₗ[Bit] E) (p : Point) :
    ∃ t : E, ∀ c x : E,
      theta (linearPointEquiv A p) (A c) (A x)+theta p c x=polar c t x :=
  alternating_form_polar (sectionDifference A p) (sectionDifference_diagonal A p)

end Atlas.Rudvalis

