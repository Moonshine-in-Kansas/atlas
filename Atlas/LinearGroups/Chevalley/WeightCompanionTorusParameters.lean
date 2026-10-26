import Atlas.LinearGroups.Chevalley.WeightCompanionTorus
import Atlas.LinearGroups.Chevalley.TorusHom
/-! Actual simultaneous torus parameter homomorphism. -/
noncomputable section
namespace Atlas.Chevalley.Integral.Minuscule.Strings
variable {I Ω : Type*} [Fintype Ω] [DecidableEq Ω]
  (S : Strings I Ω) (R : Type*) [CommRing R]
theorem torusMatrixUnit_val (i : I) (a : Rˣ) :
    (S.torusMatrixUnit R i a).val = Matrix.diagonal (fun μ => (a ^ S.pairing i μ).val) := by
  rw [← S.equivMatrixHom_torus]
  change S.torusMatrix R i a = _
  exact S.torusMatrix_diagonal R i a

theorem torusMatrixUnit_mul (i : I) (a c : Rˣ) :
    S.torusMatrixUnit R i (a*c) = S.torusMatrixUnit R i a * S.torusMatrixUnit R i c := by
  apply Units.ext
  simp only [Units.val_mul, torusMatrixUnit_val, Matrix.diagonal_mul_diagonal,
    mul_zpow]

theorem torusMatrixUnit_commute (i j : I) (a c : Rˣ) :
    Commute (S.torusMatrixUnit R i a) (S.torusMatrixUnit R j c) := by
  apply Units.ext
  simp only [Units.val_mul, torusMatrixUnit_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext μ
  exact mul_comm _ _
end Atlas.Chevalley.Integral.Minuscule.Strings

universe u
namespace Atlas.Chevalley
open Classical Integral Integral.Minuscule
variable {ι M N κ : Type u} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [AddCommGroup N]
  (P : RootPairing ι ℤ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (O : κ → Finset (WeightLattice P))
  (hclosed : ∀ a i μ, μ ∈ O a → weightReflection P i μ ∈ O a)
  (hmin : ∀ a μ, μ ∈ O a → ∀ i,
    μ (corootElement P i) = -1 ∨ μ (corootElement P i) = 0 ∨ μ (corootElement P i) = 1)
  (R : Type*) [CommRing R]

theorem weightCompanionTorus_mul (i : b.support) (a c : Rˣ) :
    weightCompanionTorus P b O hclosed hmin R i (a*c) =
      weightCompanionTorus P b O hclosed hmin R i a *
        weightCompanionTorus P b O hclosed hmin R i c := by
  apply Subtype.ext
  apply Prod.ext
  · exact adjointTorus_mul P b R i a c
  · funext k
    exact (stringsOfWeightOrbit P (O k) (hclosed k) (hmin k)).torusMatrixUnit_mul R i.val a c

theorem weightCompanionTorus_commute (i j : b.support) (a c : Rˣ) :
    Commute (weightCompanionTorus P b O hclosed hmin R i a)
      (weightCompanionTorus P b O hclosed hmin R j c) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (adjointTorus_commute P b R i j a c).eq
  · funext k
    exact ((stringsOfWeightOrbit P (O k) (hclosed k) (hmin k)).torusMatrixUnit_commute R i.val j.val a c).eq

def weightCompanionTorusProduct (s : Finset b.support) (t : b.support → Rˣ) :
    WeightCompanion P b O hclosed hmin R :=
  s.noncommProd (fun i => weightCompanionTorus P b O hclosed hmin R i (t i))
    (fun i _ j _ _ => weightCompanionTorus_commute P b O hclosed hmin R i j (t i) (t j))

set_option backward.isDefEq.respectTransparency false in
def weightCompanionTorusParameters : (b.support → Rˣ) →* WeightCompanion P b O hclosed hmin R where
  toFun t := weightCompanionTorusProduct P b O hclosed hmin R Finset.univ t
  map_one' := by
    unfold weightCompanionTorusProduct
    rw [Finset.noncommProd_eq_pow_card _ _ _ 1]
    · simp
    · intro i hi
      simp [weightCompanionTorus]
  map_mul' t v := by
    unfold weightCompanionTorusProduct
    simp only [Pi.mul_apply,weightCompanionTorus_mul]
    exact Finset.noncommProd_mul_distrib
      (fun i => weightCompanionTorus P b O hclosed hmin R i (t i))
      (fun i => weightCompanionTorus P b O hclosed hmin R i (v i))
      (fun i _ j _ _ => weightCompanionTorus_commute P b O hclosed hmin R i j (t i) (t j))
      (fun i _ j _ _ => weightCompanionTorus_commute P b O hclosed hmin R i j (v i) (v j))
      (fun i _ j _ _ => weightCompanionTorus_commute P b O hclosed hmin R i j (v i) (t j))

set_option backward.isDefEq.respectTransparency false in
theorem weightCompanionTorusProduct_adjoint (s : Finset b.support) (t : b.support → Rˣ) :
    (weightCompanionTorusProduct P b O hclosed hmin R s t).val.1 =
      adjointTorusProduct P b R s t := by
  induction s using Finset.induction_on with
  | empty => simp [weightCompanionTorusProduct, adjointTorusProduct]
  | @insert i s hi ih =>
    unfold weightCompanionTorusProduct adjointTorusProduct at *
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hi]
    change (weightCompanionTorus P b O hclosed hmin R i (t i)).val.1 * _ = _
    rw [weightCompanionTorus_adjoint, ih]

set_option backward.isDefEq.respectTransparency false in
theorem weightCompanionTorusProduct_minuscule (s : Finset b.support) (t : b.support → Rˣ)
    (k : κ) :
    ((weightCompanionTorusProduct P b O hclosed hmin R s t).val.2 k).val =
      Matrix.diagonal (fun μ : WeightOrbit P (O k) =>
        ∏ i ∈ s, ((t i) ^ μ.val (corootElement P i.val)).val) := by
  induction s using Finset.induction_on with
  | empty => simp [weightCompanionTorusProduct]
  | @insert i s hi ih =>
    unfold weightCompanionTorusProduct at *
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]
    change ((weightCompanionTorus P b O hclosed hmin R i (t i)).val.2 k).val * _ = _
    rw [weightCompanionTorus_minuscule, Strings.torusMatrixUnit_val, ih,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext μ
    simp only [Finset.prod_insert hi, stringsOfWeightOrbit_pairing]

end Atlas.Chevalley
