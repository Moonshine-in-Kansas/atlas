import Atlas.Lattices.ConwayWales.CyclicCodeAction
import Atlas.Lattices.ConwayWales.CyclicComponentSizes

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.ConwayWales
open Polynomial
local instance : Fact (1 < (4 : ℕ)) := ⟨by decide⟩

abbrev BlockCoordinate := Fin 4 × Fin 2

def codePolynomial (c : FrameCodeSpace) (u : BlockCoordinate) : Polynomial (ZMod 4) :=
  ∑ r : Row, Polynomial.C (c (r,u)) * X ^ r.val

theorem cyclicPolynomial_monic : (X^7-1 : Polynomial (ZMod 4)).Monic := by
  monicity <;> norm_num

theorem cyclicPolynomial_degree : (X^7-1 : Polynomial (ZMod 4)).natDegree = 7 := by
  compute_degree <;> norm_num <;> decide

/-- The coefficient model of each of the eight cyclic coordinate polynomials. -/
def cyclicCoefficientEquiv : CyclicRing ≃ₗ[ZMod 4] (Row → ZMod 4) := by
  have e := (AdjoinRoot.powerBasisAux' cyclicPolynomial_monic).equivFun
  have hd := cyclicPolynomial_degree
  have e' := e.trans (LinearEquiv.funCongrLeft (ZMod 4) (ZMod 4) (finCongr hd.symm))
  exact
    { toFun := e'
      invFun := e'.symm
      left_inv := e'.left_inv
      right_inv := e'.right_inv
      map_add' := e'.map_add
      map_smul' := e'.map_smul }

theorem codePolynomial_degree (c : FrameCodeSpace) (u : BlockCoordinate) :
    (codePolynomial c u).degree < 7 :=
  Polynomial.degree_sum_fin_lt (fun r : Row => c (r,u))

theorem cyclicCoefficientEquiv_mk (c : FrameCodeSpace) (u : BlockCoordinate) (r : Row) :
    cyclicCoefficientEquiv (Ideal.Quotient.mk _ (codePolynomial c u)) r = c (r,u) := by
  change (AdjoinRoot.modByMonicHom cyclicPolynomial_monic
    (AdjoinRoot.mk (X^7-1) (codePolynomial c u))).coeff r.val = _
  rw [AdjoinRoot.modByMonicHom_mk]
  have hm : codePolynomial c u %ₘ (X^7-1) = codePolynomial c u :=
    (Polynomial.modByMonic_eq_self_iff cyclicPolynomial_monic).mpr (by
    rw [Polynomial.degree_eq_natDegree cyclicPolynomial_monic.ne_zero, cyclicPolynomial_degree]
    exact codePolynomial_degree c u)
  rw [hm]
  simp only [codePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  simpa only [Fin.ext_iff, eq_comm, Finset.mem_univ, ite_true] using (Finset.sum_ite_eq' Finset.univ r (fun i : Row => c (i,u)))

/-- The actual coordinate-polynomial model of the entire 56-coordinate ambient space. -/
def codePolynomialEquiv : FrameCodeSpace ≃ₗ[ZMod 4] (BlockCoordinate → CyclicRing) where
  toFun c u := cyclicCoefficientEquiv.symm (fun r => c (r,u))
  invFun p i := cyclicCoefficientEquiv (p i.2) i.1
  left_inv c := by
    funext ⟨r,u⟩
    exact congrFun (cyclicCoefficientEquiv.apply_symm_apply (fun r => c (r,u))) r
  right_inv p := by
    funext u
    exact cyclicCoefficientEquiv.symm_apply_apply (p u)
  map_add' c d := by
    funext u
    exact cyclicCoefficientEquiv.symm.map_add _ _
  map_smul' a c := by
    funext u
    exact cyclicCoefficientEquiv.symm.map_smul a _

theorem codePolynomialEquiv_apply (c : FrameCodeSpace) (u : BlockCoordinate) :
    codePolynomialEquiv c u = Ideal.Quotient.mk _ (codePolynomial c u) := by
  apply cyclicCoefficientEquiv.injective
  funext r
  rw [cyclicCoefficientEquiv_mk]
  exact congrFun (cyclicCoefficientEquiv.apply_symm_apply (fun r => c (r,u))) r

/-- The image of the original lattice code in the eight cyclic polynomial coordinates. -/
def framePolynomialCode : Submodule (ZMod 4) (BlockCoordinate → CyclicRing) :=
  frameCodeModule.map codePolynomialEquiv.toLinearMap

theorem framePolynomialCode_mem (c : FrameCodeSpace) (hc : c ∈ frameCode) :
    codePolynomialEquiv c ∈ framePolynomialCode :=
  ⟨c,hc,rfl⟩

end Atlas.ConwayWales

