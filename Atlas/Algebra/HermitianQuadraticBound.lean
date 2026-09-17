import Atlas.Algebra.SymmetricMatrixMetric
import Mathlib.Analysis.Complex.Order

noncomputable section
namespace Atlas.Algebra
open scoped BigOperators ComplexConjugate ComplexOrder

/-- Symbolic positivity of the symmetric-square Gram matrix. -/
theorem symmetricMatrixSquare_gram_posDef {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (v : J → EuclideanSpace ℂ I) (a : ℝ) (ha : 1<a)
    (hn : ∀ i, inner ℂ (v i) (v i)=(a : ℂ))
    (hp : ∀ i j, i≠j → (inner ℂ (v i) (v j))^2=star (inner ℂ (v i) (v j))) :
    (Matrix.gram ℂ (fun i => symmetricMatrixEuclidean I (euclideanSymmetricSquare (v i)))).PosDef := by
  rw [symmetricMatrixSquare_gram v a hn hp]
  apply Matrix.PosDef.add_posSemidef
  · apply Matrix.PosDef.diagonal
    intro i
    exact Complex.zero_lt_real.mpr (by nlinarith)
  · exact Matrix.posSemidef_gram ℂ (fun i => euclideanConjugate (v i))

/-- Independence holds in the actual symmetric-matrix vector space, whose
Frobenius realization has the squared original pairing. -/
theorem symmetricMatrixSquare_linearIndependent {I J : Type*} [Fintype I] [Fintype J]
    (v : J → EuclideanSpace ℂ I) (a : ℝ) (ha : 1<a)
    (hn : ∀ i, inner ℂ (v i) (v i)=(a : ℂ))
    (hp : ∀ i j, i≠j → (inner ℂ (v i) (v j))^2=star (inner ℂ (v i) (v j))) :
    LinearIndependent ℂ (fun i => euclideanSymmetricSquare (v i)) := by
  classical
  exact LinearIndependent.of_comp (symmetricMatrixEuclidean I)
    (Matrix.linearIndependent_of_posDef_gram (symmetricMatrixSquare_gram_posDef v a ha hn hp))

/-- The quadratic absolute bound for a finite Hermitian configuration. It uses
symbolic Gram positivity, never a rank computation on the family matrix. -/
theorem hermitian_quadratic_bound {I J : Type*} [Fintype I] [Fintype J]
    (v : J → EuclideanSpace ℂ I) (a : ℝ) (ha : 1<a)
    (hn : ∀ i, inner ℂ (v i) (v i)=(a : ℂ))
    (hp : ∀ i j, i≠j → (inner ℂ (v i) (v j))^2=star (inner ℂ (v i) (v j))) :
    Fintype.card J≤(Fintype.card I+1).choose 2 := by
  have h := (symmetricMatrixSquare_linearIndependent v a ha hn hp).fintype_card_le_finrank
  rwa [symmetricMatrixSpace_finrank] at h

theorem complex_cube_pairing_square (z : ℂ) (hz : z=0 ∨ z^3=1) : z^2=star z := by
  rcases hz with rfl | hz
  · simp
  have hn := Complex.norm_eq_one_of_pow_eq_one hz (by decide : (3 : ℕ)≠0)
  have hunit : star z*z=1 := by
    change (starRingEnd ℂ) z * z = 1
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hn]
    norm_num
  have hnz : z≠0 := by intro he; simp [he] at hz
  apply mul_right_cancel₀ hnz
  rw [← pow_succ,hz,hunit]

/-- Source form of the bound: common squared norm greater than one, and every
off-diagonal pairing zero or a cube root of unity. -/
theorem hermitian_cube_root_quadratic_bound {I J : Type*} [Fintype I] [Fintype J]
    (v : J → EuclideanSpace ℂ I) (a : ℝ) (ha : 1<a)
    (hn : ∀ i, inner ℂ (v i) (v i)=(a : ℂ))
    (hp : ∀ i j, i≠j → inner ℂ (v i) (v j)=0 ∨ (inner ℂ (v i) (v j))^3=1) :
    Fintype.card J≤(Fintype.card I+1).choose 2 :=
  hermitian_quadratic_bound v a ha hn (fun i j hij => complex_cube_pairing_square _ (hp i j hij))

end Atlas.Algebra
