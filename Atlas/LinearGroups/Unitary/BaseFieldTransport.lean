import Atlas.LinearGroups.Unitary.Hermitian
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Actual unitary matrix transport under changes of both finite fields -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F F' K L : Type*} [Field F] [Field F'] [Field K] [Field L]
  [Finite F] [Finite F'] [Finite K] [Finite L] [Algebra F K] [Algebra F' L]
variable {n : ℕ}

/-- Canonical Frobenius transport depends on the actual base cardinality. -/
theorem map_conjugation_baseChange (e : K ≃+* L) (hcard : Nat.card F = Nat.card F')
    (x : K) : e (conjugation F K x) = conjugation F' L (e x) := by
  simp only [conjugation_apply, map_pow, hcard]

theorem map_hermitian_baseChange (e : K ≃+* L) (hcard : Nat.card F = Nat.card F') (v w : Fin n → K) :
    e (hermitian F K v w) = hermitian F' L (fun i => e (v i)) (fun i => e (w i)) := by
  simp [hermitian, map_sum, map_mul, map_conjugation_baseChange e hcard]

theorem map_mem_unitary_baseChange (e : K ≃+* L) (hcard : Nat.card F = Nat.card F')
    (hK : Module.finrank F K = 2) (hL : Module.finrank F' L = 2)
    (A : Matrix (Fin n) (Fin n) K)
    (hA : letI := conjugationStarRing F K hK; A ∈ Matrix.unitaryGroup (Fin n) K) :
    letI := conjugationStarRing F' L hL
    A.map e ∈ Matrix.unitaryGroup (Fin n) L := by
  letI := conjugationStarRing F K hK
  letI := conjugationStarRing F' L hL
  apply Matrix.mem_unitaryGroup_iff'.mpr
  have h : Aᴴ * A = 1 := (Matrix.mem_unitaryGroup_iff'.mp hA)
  have he := congrArg (fun B : Matrix (Fin n) (Fin n) K => B.map e) h
  have hm : (Aᴴ).map e = (A.map e)ᴴ := by
    ext i j
    exact map_conjugation_baseChange e hcard (A j i)
  change e.toRingHom.mapMatrix (Aᴴ * A) = e.toRingHom.mapMatrix 1 at he
  rw [map_mul, map_one] at he
  change (Aᴴ).map e * A.map e = 1 at he
  rw [hm] at he
  exact he

/-- Entrywise transport is a multiplicative equivalence of the actual U carriers. -/
def unitaryBaseChangeEquiv (e : K ≃+* L) (hcard : Nat.card F = Nat.card F')
    (hK : Module.finrank F K = 2) (hL : Module.finrank F' L = 2) (n : ℕ) :
    U F K n hK ≃* U F' L n hL where
  toFun g := ⟨g.val.map e, map_mem_unitary_baseChange e hcard hK hL g.val g.prop⟩
  invFun g := ⟨g.val.map e.symm, map_mem_unitary_baseChange e.symm hcard.symm hL hK g.val g.prop⟩
  left_inv g := by apply Subtype.ext; ext i j; exact e.symm_apply_apply _
  right_inv g := by apply Subtype.ext; ext i j; exact e.apply_symm_apply _
  map_mul' g h := by
    apply Subtype.ext
    exact e.toRingHom.mapMatrix.map_mul g.val h.val

/-- The same entrywise transport preserves determinant one. -/
def specialUnitaryBaseChangeEquiv (e : K ≃+* L) (hcard : Nat.card F = Nat.card F')
    (hK : Module.finrank F K = 2) (hL : Module.finrank F' L = 2) (n : ℕ) :
    SU F K n hK ≃* SU F' L n hL where
  toFun g := ⟨g.val.map e, map_mem_unitary_baseChange e hcard hK hL g.val g.prop.1, by
    change (g.val.map e).det = 1
    have he := e.toRingHom.map_det g.val
    change e g.val.det = (g.val.map e).det at he
    rw [← he, show g.val.det = 1 from g.prop.2, map_one]⟩
  invFun g := ⟨g.val.map e.symm, map_mem_unitary_baseChange e.symm hcard.symm hL hK g.val g.prop.1, by
    change (g.val.map e.symm).det = 1
    have he := e.symm.toRingHom.map_det g.val
    change e.symm g.val.det = (g.val.map e.symm).det at he
    rw [← he, show g.val.det = 1 from g.prop.2, map_one]⟩
  left_inv g := by apply Subtype.ext; ext i j; exact e.symm_apply_apply _
  right_inv g := by apply Subtype.ext; ext i j; exact e.apply_symm_apply _
  map_mul' g h := by
    apply Subtype.ext
    exact e.toRingHom.mapMatrix.map_mul g.val h.val

/-- The actual center quotient is transported through the actual special group. -/
def projectiveUnitaryBaseChangeEquiv (e : K ≃+* L) (hcard : Nat.card F = Nat.card F')
    (hK : Module.finrank F K = 2) (hL : Module.finrank F' L = 2) (n : ℕ) :
    PSU F K n hK ≃* PSU F' L n hL :=
  QuotientGroup.congr _ _ (specialUnitaryBaseChangeEquiv e hcard hK hL n)
    (Subgroup.map_center_eq (specialUnitaryBaseChangeEquiv e hcard hK hL n))

/-- Finite-field uniqueness supplies an actual ring equivalence of the quadratic
fields when the base cardinalities agree. -/
def quadraticFieldEquivOfBaseCardEq
    (hK : Module.finrank F K = 2) (hL : Module.finrank F' L = 2)
    (hcard : Nat.card F = Nat.card F') : K ≃+* L := by
  let := Fintype.ofFinite K
  let := Fintype.ofFinite L
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_extension hK, card_extension hL, hcard]

/-- Independence of finite-field choices is an actual matrix-induced equivalence,
not recognition from the group order. -/
def projectiveUnitaryEquivOfBaseCardEq
    (hK : Module.finrank F K = 2) (hL : Module.finrank F' L = 2)
    (hcard : Nat.card F = Nat.card F') (n : ℕ) :
    PSU F K n hK ≃* PSU F' L n hL :=
  projectiveUnitaryBaseChangeEquiv
    (quadraticFieldEquivOfBaseCardEq hK hL hcard) hcard hK hL n

end Atlas.Unitary

