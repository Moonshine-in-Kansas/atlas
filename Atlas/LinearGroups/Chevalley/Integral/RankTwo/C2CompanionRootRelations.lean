import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2MinusculeCorrespondence
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2RootRelations

/-! Relations in the actual selected C2 companion are
proved on both literal blocks. They are not lifted along an assumed injective
adjoint projection. Every coefficient identity is integral before base change. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo.C2Minuscule
open ClassicalData
local instance c2CompanionRelationsRootDecidableEq : DecidableEq (BRoot 2) :=
  Classical.decEq _
local instance c2CompanionRelationsBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
open scoped commutatorElement
local instance c2CompanionRelationsRankNeZero : NeZero C2.rank := ⟨by decide⟩
set_option maxRecDepth 8192
variable {R : Type*} [CommRing R]

/-- Explicit dispatcher bridge, proved once at a single generator rather than
normalizing a whole three-factor group word. -/
theorem rho_X (k : Fin 2) (t : R) :
    selectedWeightCompanionRho C2 R (selectedWeightCompanionX C2 R k t) =
      adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t := by
  rfl

theorem rho_Y (k : Fin 2) (t : R) :
    selectedWeightCompanionRho C2 R (selectedWeightCompanionY C2 R k t) =
      adjointY (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) t := by
  rfl

def weyl (k : Fin 2) : Companion R :=
  selectedWeightCompanionX C2 R k 1 * selectedWeightCompanionY C2 R k (-1) *
    selectedWeightCompanionX C2 R k 1

def rootZ (t : R) : Companion R :=
  weyl 1 * selectedWeightCompanionX C2 R 0 t * (weyl 1)⁻¹

def rootW (t : R) : Companion R :=
  weyl 0 * selectedWeightCompanionX C2 R 1 t * (weyl 0)⁻¹

theorem rho_weyl (k : Fin 2) :
    selectedWeightCompanionRho C2 R (weyl k) =
      adjointWeyl (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 k) 1 := by
  simp only [weyl, map_mul, rho_X, rho_Y, adjointWeyl,
    Units.val_one, show (1 : Rˣ).inv = 1 from rfl]
  rfl

theorem rho_Z (t : R) : selectedWeightCompanionRho C2 R (rootZ t) = c2Z t := by
  simp only [rootZ, map_mul, map_inv, rho_weyl, c2Z]
  rfl

theorem rho_W (t : R) : selectedWeightCompanionRho C2 R (rootW t) = c2W t := by
  simp only [rootW, map_mul, map_inv, rho_weyl, c2W]
  rfl

theorem matrix_weyl_short :
    weightMatrixHom R (weyl 0) = (Int.castRingHom R).mapMatrix na := by
  have hx := matrix_xshort (R := R) (1 : R)
  have hy := matrix_yshort (R := R) (-1 : R)
  calc
    weightMatrixHom R (weyl 0) =
        weightMatrixHom R (selectedWeightCompanionX C2 R 0 1) *
          weightMatrixHom R (selectedWeightCompanionY C2 R 0 (-1)) *
          weightMatrixHom R (selectedWeightCompanionX C2 R 0 1) := by
      simp only [weyl, map_mul]
      rfl
    _ = XA (1 : R) * YA (-1 : R) * XA (1 : R) :=
      congrArg₂ (· * ·) (congrArg₂ (· * ·) hx hy) hx
    _ = (Int.castRingHom R).mapMatrix na := by
      have h := congrArg ((Int.castRingHom R).mapMatrix (m := Fin 4)) na_word
      simpa only [XA, YA, map_mul, map_add, map_sub, map_neg, map_one, one_smul,
        neg_one_smul, sub_eq_add_neg, RingHom.mapMatrix_apply] using h

theorem matrix_weyl_long :
    weightMatrixHom R (weyl 1) = (Int.castRingHom R).mapMatrix nb := by
  have hx := matrix_xlong (R := R) (1 : R)
  have hy := matrix_ylong (R := R) (-1 : R)
  calc
    weightMatrixHom R (weyl 1) =
        weightMatrixHom R (selectedWeightCompanionX C2 R 1 1) *
          weightMatrixHom R (selectedWeightCompanionY C2 R 1 (-1)) *
          weightMatrixHom R (selectedWeightCompanionX C2 R 1 1) := by
      simp only [weyl, map_mul]
      rfl
    _ = XB (1 : R) * YB (-1 : R) * XB (1 : R) :=
      congrArg₂ (· * ·) (congrArg₂ (· * ·) hx hy) hx
    _ = (Int.castRingHom R).mapMatrix nb := by
      have h := congrArg ((Int.castRingHom R).mapMatrix (m := Fin 4)) nb_word
      simpa only [XB, YB, map_mul, map_add, map_sub, map_neg, map_one, one_smul,
        neg_one_smul, sub_eq_add_neg, RingHom.mapMatrix_apply] using h

private theorem matrix_inverse_of_integral (g : Companion R)
    (A B : Matrix (Fin 4) (Fin 4) ℤ)
    (hg : weightMatrixHom R g = (Int.castRingHom R).mapMatrix A)
    (hAB : A * B = 1) :
    weightMatrixHom R g⁻¹ = (Int.castRingHom R).mapMatrix B := by
  let f := weightMatrixHom R
  let c := (Int.castRingHom R).mapMatrix (m := Fin 4)
  have h : f g * c B = 1 := by rw [hg, ← map_mul, hAB, map_one]
  calc
    f g⁻¹ = f g⁻¹ * (f g * c B) := by rw [h, mul_one]
    _ = (f g⁻¹ * f g) * c B := (mul_assoc _ _ _).symm
    _ = c B := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

theorem matrix_weyl_short_inv :
    weightMatrixHom R (weyl 0)⁻¹ = (Int.castRingHom R).mapMatrix naInv :=
  matrix_inverse_of_integral _ _ _ matrix_weyl_short na_inverse

theorem matrix_weyl_long_inv :
    weightMatrixHom R (weyl 1)⁻¹ = (Int.castRingHom R).mapMatrix nbInv :=
  matrix_inverse_of_integral _ _ _ matrix_weyl_long nb_inverse

private theorem conjugate_linear (N NI E Z : Matrix (Fin 4) (Fin 4) ℤ)
    (h0 : N * NI = 1) (h1 : N * E * NI = Z) (t : R) :
    (Int.castRingHom R).mapMatrix N *
      (1 + t • (Int.castRingHom R).mapMatrix E) *
      (Int.castRingHom R).mapMatrix NI =
    1 + t • (Int.castRingHom R).mapMatrix Z := by
  let c := (Int.castRingHom R).mapMatrix (m := Fin 4)
  change c N * (1 + t • c E) * c NI = _
  calc
    _ = c N * c NI + t • (c N * c E * c NI) := by
      simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc]
    _ = _ := by rw [← map_mul, ← map_mul, ← map_mul, h0, h1, map_one]

theorem matrix_Z (t : R) : weightMatrixHom R (rootZ t) = Z t := by
  rw [rootZ, map_mul, map_mul, matrix_weyl_long, matrix_xshort, matrix_weyl_long_inv]
  exact conjugate_linear nb nbInv ea za nb_inverse nb_ea_conjugate t

theorem matrix_W (t : R) : weightMatrixHom R (rootW t) = W t := by
  rw [rootW, map_mul, map_mul, matrix_weyl_short, matrix_xlong, matrix_weyl_short_inv]
  exact conjugate_linear na naInv eb wb na_inverse na_eb_conjugate t

/-- The short-short product identity holds on both actual summands. -/
theorem companion_short_short_product (s t : R) :
    selectedWeightCompanionX C2 R 0 s * rootZ t =
      rootW (-2*s*t) * rootZ t * selectedWeightCompanionX C2 R 0 s := by
  apply ext R
  · simp only [map_mul, rho_Z, rho_W]
    exact c2_short_short_product s t
  · simp only [map_mul, matrix_xshort, matrix_Z, matrix_W]
    exact same_root_relation s t

/-- The mixed product identity holds in the selected companion itself. -/
theorem companion_short_long_product (s t : R) :
    selectedWeightCompanionX C2 R 0 s * selectedWeightCompanionX C2 R 1 t =
      rootZ (-s*t) * rootW (s^2*t) * selectedWeightCompanionX C2 R 1 t *
        selectedWeightCompanionX C2 R 0 s := by
  apply ext R
  · simp only [map_mul, rho_Z, rho_W]
    exact c2_short_long_product s t
  · simp only [map_mul, matrix_xshort, matrix_xlong, matrix_Z, matrix_W]
    exact mixed_root_relation s t

private theorem commutator_of_product {G : Type*} [Group G] (x y z : G)
    (h : x*y = z*y*x) : ⁅x,y⁆ = z := by
  rw [commutatorElement_def, h]
  group

theorem companion_short_short_commutator (s t : R) :
    ⁅selectedWeightCompanionX C2 R 0 s, rootZ t⁆ = rootW (-2*s*t) :=
  commutator_of_product _ _ _ (companion_short_short_product s t)

theorem companion_short_long_commutator (s t : R) :
    ⁅selectedWeightCompanionX C2 R 0 s, selectedWeightCompanionX C2 R 1 t⁆ =
      rootZ (-s*t) * rootW (s^2*t) :=
  commutator_of_product _ _ _ (companion_short_long_product s t)

end Atlas.Chevalley.Integral.RankTwo.C2Minuscule
