import Atlas.LinearGroups.Chevalley.Comparison.F4.IntegralBasisInjection

/-! Source-only continuation of the saved integral-basis branch.

The literal `basisMatrix`, `rootPivot` and `readCoordinates` are imported
unchanged. The four Cartan coordinates are treated explicitly; all 48 root
coordinates use one symbolic signed-pivot argument. In particular, scalar
transport does not unfold the root-pivot or basis tables.

The integral left-inverse certificate is a separate prerequisite, not an
assumed hypothesis. Neither that certificate nor this file was run here.
-/
namespace Atlas.Chevalley.Comparison.F4
open scoped Matrix
noncomputable section

section Reader
variable {R : Type*} [CommRing R]

/-- Additivity of the saved coordinate reader, without expanding the 48 pivots. -/
theorem readCoordinates_add (M N : Matrix (Fin 27) (Fin 27) R) :
    readCoordinates (M + N) = readCoordinates M + readCoordinates N := by
  funext i
  change readCoordinates (M + N) i = readCoordinates M i + readCoordinates N i
  by_cases hi : i.val < 4
  · simp only [readCoordinates, dif_pos hi]
    generalize hk : (⟨i.val, hi⟩ : Fin 4) = k
    fin_cases k <;> simp [Matrix.add_apply] <;> ring
  · simp only [readCoordinates, dif_neg hi, Matrix.add_apply, mul_add]

/-- Scalar linearity uses no invertibility of any integer coefficient. -/
theorem readCoordinates_smul (t : R) (M : Matrix (Fin 27) (Fin 27) R) :
    readCoordinates (t • M) = t • readCoordinates M := by
  funext i
  change readCoordinates (t • M) i = t * readCoordinates M i
  by_cases hi : i.val < 4
  · simp only [readCoordinates, dif_pos hi]
    generalize hk : (⟨i.val, hi⟩ : Fin 4) = k
    fin_cases k <;> simp [Matrix.smul_apply, smul_eq_mul] <;> ring
  · simp only [readCoordinates, dif_neg hi, Matrix.smul_apply, smul_eq_mul]
    ring

/-- The literal reader commutes with every ring homomorphism, including
reduction modulo 2 or 3. The homomorphism need not be injective. -/
theorem readCoordinates_map {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 27) (Fin 27) R) :
    readCoordinates (M.map f) = fun i => f (readCoordinates M i) := by
  funext i
  by_cases hi : i.val < 4
  · simp only [readCoordinates, dif_pos hi]
    generalize hk : (⟨i.val, hi⟩ : Fin 4) = k
    fin_cases k <;> simp [Matrix.map_apply, map_ofNat]
  · simp only [readCoordinates, dif_neg hi, Matrix.map_apply, map_mul, map_intCast]

end Reader

variable (R : Type*) [CommRing R]

/-- The unchanged literal integral matrices, with coefficients cast to R. -/
def basisOver (i : Fin 52) : Matrix (Fin 27) (Fin 27) R :=
  (basisMatrix i).map (Int.castRingHom R)

/-- The same 52-coordinate linear combination used by the saved conjugation
and Albert-lift candidates. This definition asserts no root compatibility. -/
def matrixEmbedding : (Fin 52 → R) →ₗ[R] Matrix (Fin 27) (Fin 27) R where
  toFun v := ∑ i : Fin 52, v i • basisOver R i
  map_add' v w := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t v := by simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

def coordinateProjection : Matrix (Fin 27) (Fin 27) R →ₗ[R] (Fin 52 → R) where
  toFun := readCoordinates
  map_add' M N := readCoordinates_add M N
  map_smul' t M := readCoordinates_smul t M

/-- Base change of the exact integer certificate; no rank or field-order
argument, and no characteristic restriction. -/
theorem coordinateProjection_basis (i j : Fin 52) :
    coordinateProjection R (basisOver R j) i = if i=j then 1 else 0 := by
  change readCoordinates ((basisMatrix j).map (Int.castRingHom R)) i = _
  rw [readCoordinates_map]
  simpa only [apply_ite, map_one, map_zero] using
    congrArg (Int.castRingHom R) (readCoordinates_basis i j)

/-- The coordinate reader is a left inverse over every commutative ring. -/
theorem coordinateProjection_matrixEmbedding (v : Fin 52 → R) :
    coordinateProjection R (matrixEmbedding R v) = v := by
  funext i
  change coordinateProjection R (∑ j : Fin 52, v j • basisOver R j) i = v i
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    coordinateProjection_basis]
  simp

/-- Injectivity of the literal 52-space in 27-by-27 matrices, including
characteristics 2 and 3. This is not faithfulness of a group conjugation action. -/
theorem matrixEmbedding_injective : Function.Injective (matrixEmbedding R) :=
  Function.LeftInverse.injective (coordinateProjection_matrixEmbedding R)

end
end Atlas.Chevalley.Comparison.F4
