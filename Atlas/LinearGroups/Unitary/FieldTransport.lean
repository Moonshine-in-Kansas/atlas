import Atlas.LinearGroups.Unitary.Hermitian

/-! # Actual unitary matrix transport under quadratic-field isomorphisms -/
noncomputable section
namespace Atlas.Unitary
open Matrix Atlas.FiniteQuadratic
variable {F K L : Type*} [Field F] [Field K] [Field L]
  [Finite F] [Finite K] [Finite L] [Algebra F K] [Algebra F L]
variable {n : ℕ}

theorem map_hermitian (e : K ≃ₐ[F] L) (v w : Fin n → K) :
    e (hermitian F K v w) = hermitian F L (fun i => e (v i)) (fun i => e (w i)) := by
  simp [hermitian, map_sum, map_mul, map_conjugation]

theorem map_mem_unitary (e : K ≃ₐ[F] L)
    (hK : Module.finrank F K = 2) (hL : Module.finrank F L = 2)
    (A : Matrix (Fin n) (Fin n) K)
    (hA : letI := conjugationStarRing F K hK; A ∈ Matrix.unitaryGroup (Fin n) K) :
    letI := conjugationStarRing F L hL
    A.map e ∈ Matrix.unitaryGroup (Fin n) L := by
  letI := conjugationStarRing F K hK
  letI := conjugationStarRing F L hL
  apply Matrix.mem_unitaryGroup_iff'.mpr
  have h : Aᴴ * A = 1 := (Matrix.mem_unitaryGroup_iff'.mp hA)
  have he := congrArg (fun B : Matrix (Fin n) (Fin n) K => B.map e) h
  have hm : (Aᴴ).map e = (A.map e)ᴴ := by
    ext i j
    exact map_conjugation e (A j i)
  change e.toRingHom.mapMatrix (Aᴴ * A) = e.toRingHom.mapMatrix 1 at he
  rw [map_mul, map_one] at he
  change (Aᴴ).map e * A.map e = 1 at he
  rw [hm] at he
  exact he

/-- Entrywise transport is a multiplicative equivalence of the actual U carriers. -/
def unitaryFieldEquiv (e : K ≃ₐ[F] L)
    (hK : Module.finrank F K = 2) (hL : Module.finrank F L = 2) (n : ℕ) :
    U F K n hK ≃* U F L n hL where
  toFun g := ⟨g.val.map e, map_mem_unitary e hK hL g.val g.prop⟩
  invFun g := ⟨g.val.map e.symm, map_mem_unitary e.symm hL hK g.val g.prop⟩
  left_inv g := by apply Subtype.ext; ext i j; exact e.symm_apply_apply _
  right_inv g := by apply Subtype.ext; ext i j; exact e.apply_symm_apply _
  map_mul' g h := by
    apply Subtype.ext
    exact e.toRingHom.mapMatrix.map_mul g.val h.val

/-- The same entrywise transport preserves determinant one. -/
def specialUnitaryFieldEquiv (e : K ≃ₐ[F] L)
    (hK : Module.finrank F K = 2) (hL : Module.finrank F L = 2) (n : ℕ) :
    SU F K n hK ≃* SU F L n hL where
  toFun g := ⟨g.val.map e, map_mem_unitary e hK hL g.val g.prop.1, by
    change (g.val.map e).det = 1
    have he := e.toRingHom.map_det g.val
    change e g.val.det = (g.val.map e).det at he
    rw [← he, show g.val.det = 1 from g.prop.2, map_one]⟩
  invFun g := ⟨g.val.map e.symm, map_mem_unitary e.symm hL hK g.val g.prop.1, by
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
def projectiveUnitaryFieldEquiv (e : K ≃ₐ[F] L)
    (hK : Module.finrank F K = 2) (hL : Module.finrank F L = 2) (n : ℕ) :
    PSU F K n hK ≃* PSU F L n hL :=
  QuotientGroup.congr _ _ (specialUnitaryFieldEquiv e hK hL n)
    (Subgroup.map_center_eq (specialUnitaryFieldEquiv e hK hL n))

end Atlas.Unitary
