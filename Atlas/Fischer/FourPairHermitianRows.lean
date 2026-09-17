import Atlas.Fischer.CoordinateHermitianSums
import Atlas.Fischer.OctadicHyperplaneAxisPairings

noncomputable section
namespace Atlas.Fischer
attribute [local instance] Classical.propDecidable

/-- The literal J-2I row on either half of a four-by-two orthonormal family. -/
def fourPairDifference {ι : Type*} [Fintype ι] (v : ι × Fin 2 → Coordinates)
    (i : ι) (a : Fin 2) : Coordinates := (∑ j, v (j,a)) - (2 : Scalar) • v (i,a)

theorem fourPairDifference_pairing {ι : Type*} [Fintype ι] (hc : Fintype.card ι = 4)
    (v : ι × Fin 2 → Coordinates)
    (hv : ∀ p q, hermitian (v p) (v q) = if p = q then 1 else 0)
    (i j : ι) (a b : Fin 2) :
    hermitian (fourPairDifference v i a) (fourPairDifference v j b) =
      if (i,a) = (j,b) then 4 else 0 := by
  have hsum (a b : Fin 2) : hermitian (∑ k, v (k,a)) (∑ l, v (l,b)) =
      if a = b then 4 else 0 := by
    simp only [hermitian_sum_left, hermitian_sum_right, hv, Prod.mk.injEq]
    by_cases hab : a = b
    · subst b
      simp [hc]
    · simp [hab]
  have hleft (i : ι) (a b : Fin 2) : hermitian (∑ k, v (k,a)) (v (i,b)) =
      if a = b then 1 else 0 := by
    simp only [hermitian_sum_left, hv, Prod.mk.injEq]
    by_cases hab : a = b
    · subst b
      simp
    · simp [hab]
  have hright (j : ι) (a b : Fin 2) : hermitian (v (j,a)) (∑ k, v (k,b)) =
      if a = b then 1 else 0 := by
    simp only [hermitian_sum_right, hv, Prod.mk.injEq]
    by_cases hab : a = b
    · subst b
      simp
    · simp [hab]
  simp only [fourPairDifference, hermitian_sub_left, hermitian_sub_right,
    hermitian_smul_left, hermitian_smul_right, hsum, hleft, hright, hv,
    star_ofNat, Prod.mk.injEq]
  by_cases hij : i = j <;> by_cases hab : a = b <;> simp [hij, hab] <;> ring

/-- The two theta-coupled rows, before identifying them with an actual root map. -/
def fourPairThetaRow {ι : Type*} [Fintype ι] (v : ι × Fin 2 → Coordinates)
    (i : ι) (a : Fin 2) : Coordinates :=
  (1 / 4 : Scalar) • fourPairDifference v i a +
    (theta / 4) • fourPairDifference v i (1-a)

theorem fourPairThetaRow_orthonormal {ι : Type*} [Fintype ι] (hc : Fintype.card ι = 4)
    (v : ι × Fin 2 → Coordinates)
    (hv : ∀ p q, hermitian (v p) (v q) = if p = q then 1 else 0)
    (i j : ι) (a b : Fin 2) :
    hermitian (fourPairThetaRow v i a) (fourPairThetaRow v j b) =
      if (i,a) = (j,b) then 1 else 0 := by
  simp only [fourPairThetaRow, hermitian_add_left, hermitian_add_right,
    hermitian_smul_left, hermitian_smul_right, fourPairDifference_pairing hc v hv,
    star_div₀, star_one, star_ofNat, theta_conjugate]
  fin_cases a <;> fin_cases b <;> by_cases hij : i = j <;>
    simp [Prod.mk.injEq, hij] <;> ring_nf <;> simp [theta_sq] <;> norm_num

end Atlas.Fischer
