import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2ActualExponentials
import Atlas.LinearGroups.Chevalley.Integral.RankTwo.C2ConjugationConstants
import Atlas.LinearGroups.Chevalley.RankOne

/-! Literal adjoint C2 Weyl words and their conjugates,
transported from integral identities to arbitrary commutative rings. This file
requires the preceding actual exponential and integral constant files first.
No variable commutator or full-group structure theorem is asserted here. -/
noncomputable section
namespace Atlas.Chevalley.Integral.RankTwo
open ClassicalData C2IntegerTemplate
open scoped Matrix
local instance c2WeylRootDecidableEq : DecidableEq (BRoot 2) := Classical.decEq _
local instance c2WeylBaseDecidableEq : DecidableEq (baseC 1).support :=
  inferInstanceAs (DecidableEq {i : BRoot 2 // i ∈ (baseC 1).support})
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable (R : Type*) [CommRing R]

/-- The actual ten-coordinate reindexing of the existing adjoint representation. -/
def c2Reindex :
    Matrix ((baseC 1).support ⊕ BRoot 2) ((baseC 1).support ⊕ BRoot 2) R ≃ₐ[R]
      Matrix (Fin 10) (Fin 10) R :=
  Matrix.reindexAlgEquiv R R c2IndexEquiv.symm

/-- The faithful matrix map is a reindexing, not a new group construction. -/
def c2AdjointMatrixHom : Adjoint (pairingC 2) (baseC 1) R →*
    Matrix (Fin 10) (Fin 10) R where
  toFun g := c2Reindex R g.val.val
  map_one' := map_one (c2Reindex R)
  map_mul' g h := map_mul (c2Reindex R) g.val.val h.val.val

theorem c2AdjointMatrixHom_injective : Function.Injective (c2AdjointMatrixHom R) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  exact (c2Reindex R).injective hgh

variable {R}

def yaOver (t : R) : Matrix (Fin 10) (Fin 10) R :=
  omega.map (Int.castRingHom R) * xaOver t * omega.map (Int.castRingHom R)

def ybOver (t : R) : Matrix (Fin 10) (Fin 10) R :=
  omega.map (Int.castRingHom R) * xbOver t * omega.map (Int.castRingHom R)

def zOver (t : R) : Matrix (Fin 10) (Fin 10) R :=
  1 + t • za.map (Int.castRingHom R) + t^2 • za2.map (Int.castRingHom R)

def wOver (t : R) : Matrix (Fin 10) (Fin 10) R :=
  1 + t • wb.map (Int.castRingHom R) + t^2 • wb2.map (Int.castRingHom R)

theorem c2_reindex_opposition :
    c2Reindex R (oppositionOver (pairingC 2) (baseC 1) R) =
      omega.map (Int.castRingHom R) := by
  ext i j
  exact congrArg (Int.castRingHom R) (c2_opposition_entry i j)

theorem c2_reindex_raising_short (t : R) :
    c2Reindex R (raisingExponential (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 0) t) = xaOver t := by
  ext i j
  exact c2_exponential_short t i j

theorem c2_reindex_raising_long (t : R) :
    c2Reindex R (raisingExponential (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 1) t) = xbOver t := by
  ext i j
  exact c2_exponential_long t i j

theorem c2_matrix_xshort (t : R) :
    c2AdjointMatrixHom R (adjointX (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 0) t) = xaOver t := c2_reindex_raising_short t

theorem c2_matrix_xlong (t : R) :
    c2AdjointMatrixHom R (adjointX (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 1) t) = xbOver t := c2_reindex_raising_long t

theorem c2_matrix_yshort (t : R) :
    c2AdjointMatrixHom R (adjointY (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 0) t) = yaOver t := by
  change c2Reindex R (oppositionOver (pairingC 2) (baseC 1) R *
    raisingExponential (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) t *
    oppositionOver (pairingC 2) (baseC 1) R) = _
  rw [map_mul, map_mul, c2_reindex_opposition, c2_reindex_raising_short]
  rfl

theorem c2_matrix_ylong (t : R) :
    c2AdjointMatrixHom R (adjointY (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 1) t) = ybOver t := by
  change c2Reindex R (oppositionOver (pairingC 2) (baseC 1) R *
    raisingExponential (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) t *
    oppositionOver (pairingC 2) (baseC 1) R) = _
  rw [map_mul, map_mul, c2_reindex_opposition, c2_reindex_raising_long]
  rfl

theorem c2_cast_xa (t : ℤ) :
    (Int.castRingHom R).mapMatrix (xa t) = xaOver (t : R) := by
  change (Int.castRingHom R).mapMatrix (1 + t • ea + t^2 • ea2) =
    1 + (t : R) • (Int.castRingHom R).mapMatrix ea +
      (t : R)^2 • (Int.castRingHom R).mapMatrix ea2
  simp only [map_add, map_one, map_zsmul]
  rw [← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R, Int.cast_pow]

theorem c2_cast_xb (t : ℤ) :
    (Int.castRingHom R).mapMatrix (xb t) = xbOver (t : R) := by
  change (Int.castRingHom R).mapMatrix (1 + t • eb + t^2 • eb2) =
    1 + (t : R) • (Int.castRingHom R).mapMatrix eb +
      (t : R)^2 • (Int.castRingHom R).mapMatrix eb2
  simp only [map_add, map_one, map_zsmul]
  rw [← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R, Int.cast_pow]

theorem c2_cast_ya (t : ℤ) :
    (Int.castRingHom R).mapMatrix (ya t) = yaOver (t : R) := by
  simp only [ya, map_mul, c2_cast_xa]
  rfl

theorem c2_cast_yb (t : ℤ) :
    (Int.castRingHom R).mapMatrix (yb t) = ybOver (t : R) := by
  simp only [yb, map_mul, c2_cast_xb]
  rfl

/-- The actual pinned short Weyl word has the certified integral matrix. -/
theorem c2_matrix_weyl_short :
    c2AdjointMatrixHom R (adjointWeyl (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 0) 1) = (Int.castRingHom R).mapMatrix na := by
  simp only [adjointWeyl, Units.val_one, show (1 : Rˣ).inv = 1 from rfl, map_mul,
    c2_matrix_xshort, c2_matrix_yshort]
  rw [na_word_staged, map_mul, map_mul, c2_cast_xa, c2_cast_ya]
  norm_num

/-- The actual pinned long Weyl word has the certified integral matrix. -/
theorem c2_matrix_weyl_long :
    c2AdjointMatrixHom R (adjointWeyl (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 1) 1) = (Int.castRingHom R).mapMatrix nb := by
  simp only [adjointWeyl, Units.val_one, show (1 : Rˣ).inv = 1 from rfl, map_mul,
    c2_matrix_xlong, c2_matrix_ylong]
  rw [nb_word_staged, map_mul, map_mul, c2_cast_xb, c2_cast_yb]
  norm_num

private theorem matrix_inverse_of_integral (g : Adjoint (pairingC 2) (baseC 1) R)
    (A B : Matrix (Fin 10) (Fin 10) ℤ)
    (hg : c2AdjointMatrixHom R g = (Int.castRingHom R).mapMatrix A)
    (hAB : A * B = 1) :
    c2AdjointMatrixHom R g⁻¹ = (Int.castRingHom R).mapMatrix B := by
  let f := c2AdjointMatrixHom R
  let c := (Int.castRingHom R).mapMatrix (m := Fin 10)
  have h : f g * c B = 1 := by
    rw [hg, ← map_mul, hAB, map_one]
  calc
    f g⁻¹ = f g⁻¹ * (f g * c B) := by rw [h, mul_one]
    _ = (f g⁻¹ * f g) * c B := (mul_assoc _ _ _).symm
    _ = c B := by rw [← map_mul, inv_mul_cancel, map_one, one_mul]

theorem c2_matrix_weyl_short_inv :
    c2AdjointMatrixHom R (adjointWeyl (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 0) 1)⁻¹ = (Int.castRingHom R).mapMatrix naInv :=
  matrix_inverse_of_integral _ _ _ c2_matrix_weyl_short na_mul_naInv

theorem c2_matrix_weyl_long_inv :
    c2AdjointMatrixHom R (adjointWeyl (pairingC 2) (baseC 1) R
      (baseCIndexEquiv 1 1) 1)⁻¹ = (Int.castRingHom R).mapMatrix nbInv :=
  matrix_inverse_of_integral _ _ _ c2_matrix_weyl_long nb_mul_nbInv

private theorem conjugate_quadratic (N NI E E2 Z Z2 : Matrix (Fin 10) (Fin 10) ℤ)
    (h0 : N * NI = 1) (h1 : N * E * NI = Z) (h2 : N * E2 * NI = Z2)
    (t : R) :
    (Int.castRingHom R).mapMatrix N *
      (1 + t • (Int.castRingHom R).mapMatrix E +
        t^2 • (Int.castRingHom R).mapMatrix E2) *
      (Int.castRingHom R).mapMatrix NI =
    1 + t • (Int.castRingHom R).mapMatrix Z +
      t^2 • (Int.castRingHom R).mapMatrix Z2 := by
  let c := (Int.castRingHom R).mapMatrix (m := Fin 10)
  change c N * (1 + t • c E + t^2 • c E2) * c NI = _
  calc
    _ = c N * c NI + t • (c N * c E * c NI) +
        t^2 • (c N * c E2 * c NI) := by
      simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc]
    _ = _ := by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, h0, h1, h2, map_one]

/-- This is an element of the existing adjoint group, constructed by conjugation. -/
def c2Z (t : R) : Adjoint (pairingC 2) (baseC 1) R :=
  adjointWeyl (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) 1 *
    adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) t *
    (adjointWeyl (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) 1)⁻¹

/-- The second nonsimple positive root is another actual Weyl conjugate. -/
def c2W (t : R) : Adjoint (pairingC 2) (baseC 1) R :=
  adjointWeyl (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) 1 *
    adjointX (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 1) t *
    (adjointWeyl (pairingC 2) (baseC 1) R (baseCIndexEquiv 1 0) 1)⁻¹

theorem c2_matrix_Z (t : R) : c2AdjointMatrixHom R (c2Z t) = zOver t := by
  rw [c2Z, map_mul, map_mul, c2_matrix_weyl_long,
    c2_matrix_xshort, c2_matrix_weyl_long_inv]
  exact conjugate_quadratic nb nbInv ea ea2 za za2
    nb_mul_nbInv nb_ea_nbInv nb_ea2_nbInv t

theorem c2_matrix_W (t : R) : c2AdjointMatrixHom R (c2W t) = wOver t := by
  rw [c2W, map_mul, map_mul, c2_matrix_weyl_short,
    c2_matrix_xlong, c2_matrix_weyl_short_inv]
  exact conjugate_quadratic na naInv eb eb2 wb wb2
    na_mul_naInv na_eb_naInv na_eb2_naInv t

end Atlas.Chevalley.Integral.RankTwo
