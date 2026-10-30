import Atlas.LinearGroups.Chevalley.TwistedE6.MatrixCentralizerRecovery
import Atlas.FieldTheory.FiniteQuadraticExtension
import Atlas.LinearGroups.Chevalley.Integral.MinusculeStrings

/-!
Source-only adapter to the actual finite-quadratic conjugation and the
repository's minuscule root matrices. This does not apply an affine formula
to the adjoint block or assert faithfulness of a minuscule projection.
-/
noncomputable section

namespace Atlas.LinearAlgebra.MatrixCentralizer
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual quadratic conjugation is the q-th power, with q the cardinality
of the given base field. No choice of a different field of equal order. -/
theorem commute_pair_of_quadratic_extension (hdeg : Module.finrank F K = 2)
    (g A B : Matrix n n K)
    (h : ∀ u : K, Commute g
      ((1 + u • A) * (1 + Atlas.FiniteQuadratic.conjugation F K u • B))) :
    Commute g A ∧ Commute g B := by
  apply commute_pair_of_affine_product (q := Nat.card F)
    (Nat.succ_le_of_lt (Finite.one_lt_card : 1 < Nat.card F))
    (Atlas.FiniteQuadratic.card_extension hdeg) g A B
  intro u
  simpa only [Atlas.FiniteQuadratic.conjugation_apply] using h u

end Atlas.LinearAlgebra.MatrixCentralizer

namespace Atlas.Chevalley.Integral.Minuscule.Strings
open Atlas.LinearAlgebra.MatrixCentralizer
variable {I Ω : Type*} [Fintype Ω] [DecidableEq Ω] (S : Strings I Ω)

section FixedRoot
variable {R : Type*} [CommRing R]

/-- The actual minuscule root at parameter one suffices for a singleton
orbit. The nonzero sign is precisely the existing root-unit prerequisite. -/
theorem commute_step_of_root_one (i : I) (ε : ℤ) (hε : ε ≠ 0)
    (g : Matrix Ω Ω R)
    (h : Commute g (S.rootMatrixUnit R i ε hε 1).val) :
    Commute g (S.stepMatrix R i ε) := by
  apply commute_of_one_add g (S.stepMatrix R i ε)
  simpa only [rootMatrixUnit, rootMatrix, one_smul] using h

end FixedRoot

section PairedRoots
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Recovery for the ordered product of the actual minuscule root units.
Both step squares vanish by `stepMatrix_square` with hε and hδ. Commutation
of the two steps is not needed for this implication; it is needed separately
when proving that a diagram-exchanged root product is fixed. -/
theorem commute_steps_of_quadratic_pair (hdeg : Module.finrank F K = 2)
    (i j : I) (ε δ : ℤ) (hε : ε ≠ 0) (hδ : δ ≠ 0)
    (g : Matrix Ω Ω K)
    (h : ∀ u : K, Commute g
      ((S.rootMatrixUnit K i ε hε u).val *
        (S.rootMatrixUnit K j δ hδ (Atlas.FiniteQuadratic.conjugation F K u)).val)) :
    Commute g (S.stepMatrix K i ε) ∧ Commute g (S.stepMatrix K j δ) := by
  apply commute_pair_of_quadratic_extension F K hdeg g
    (S.stepMatrix K i ε) (S.stepMatrix K j δ)
  intro u
  exact h u

/-- Recovery of the entire two split minuscule root families, not only the
single parameter-one matrices. This conclusion is still blockwise. -/
theorem commute_roots_of_quadratic_pair (hdeg : Module.finrank F K = 2)
    (i j : I) (ε δ : ℤ) (hε : ε ≠ 0) (hδ : δ ≠ 0)
    (g : Matrix Ω Ω K)
    (h : ∀ u : K, Commute g
      ((S.rootMatrixUnit K i ε hε u).val *
        (S.rootMatrixUnit K j δ hδ (Atlas.FiniteQuadratic.conjugation F K u)).val)) :
    (∀ t : K, Commute g (S.rootMatrixUnit K i ε hε t).val) ∧
      (∀ t : K, Commute g (S.rootMatrixUnit K j δ hδ t).val) := by
  have hc := S.commute_steps_of_quadratic_pair F K hdeg i j ε δ hε hδ g h
  constructor
  · intro t
    exact commute_affine g (S.stepMatrix K i ε) hc.1 t
  · intro t
    exact commute_affine g (S.stepMatrix K j δ) hc.2 t

end PairedRoots
end Atlas.Chevalley.Integral.Minuscule.Strings
