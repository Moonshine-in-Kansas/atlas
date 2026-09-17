import Atlas.Algebra.SymmetricMatrixSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix

noncomputable section
namespace Atlas.Algebra
open scoped BigOperators ComplexConjugate

/-- The Frobenius realization counts each off-diagonal entry twice, which is
exactly the symmetric-square metric; no missing factor or scalar square root. -/
def symmetricMatrixEuclidean (I : Type*) [Fintype I] :
    symmetricMatrixSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ (I × I) where
  toFun M := WithLp.toLp 2 (fun ij => M.val ij.1 ij.2)
  map_add' M N := by rfl
  map_smul' a M := by rfl

def euclideanSymmetricSquare {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) :
    symmetricMatrixSpace ℂ I := symmetricMatrixSquare (fun i => v i)

def euclideanConjugate {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => star (v i))

/-- The metric on genuine symmetric rank-one matrices is the squared pairing. -/
theorem symmetricMatrixSquare_inner {I : Type*} [Fintype I]
    (v w : EuclideanSpace ℂ I) :
    inner ℂ (symmetricMatrixEuclidean I (euclideanSymmetricSquare v))
      (symmetricMatrixEuclidean I (euclideanSymmetricSquare w))=(inner ℂ v w)^2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  change (∑ ij : I × I, star (v ij.1*v ij.2)*(w ij.1*w ij.2))=
    (∑ i : I, star (v i)*w i)^2
  rw [Fintype.sum_prod_type,pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [star_mul]
  ring

theorem euclideanConjugate_inner {I : Type*} [Fintype I]
    (v w : EuclideanSpace ℂ I) :
    inner ℂ (euclideanConjugate v) (euclideanConjugate w)=star (inner ℂ v w) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  change (∑ i : I, star (star (v i))*star (w i))=star (∑ i : I, star (v i)*w i)
  simp only [star_sum,star_mul,star_star,mul_comm]

/-- The Gram identity is symbolic for any finite family of vectors. -/
theorem symmetricMatrixSquare_gram {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (v : J → EuclideanSpace ℂ I) (a : ℝ)
    (hn : ∀ i, inner ℂ (v i) (v i)=(a : ℂ))
    (hp : ∀ i j, i≠j → (inner ℂ (v i) (v j))^2=star (inner ℂ (v i) (v j))) :
    Matrix.gram ℂ (fun i => symmetricMatrixEuclidean I (euclideanSymmetricSquare (v i)))=
      Matrix.diagonal (fun _ : J => ((a^2-a : ℝ) : ℂ))+
        Matrix.gram ℂ (fun i => euclideanConjugate (v i)) := by
  ext i j
  simp only [Matrix.gram_apply,symmetricMatrixSquare_inner,Matrix.add_apply,
    euclideanConjugate_inner,Matrix.diagonal_apply]
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl,hn]
    simp
  · rw [if_neg hij,hp i j hij,zero_add]

end Atlas.Algebra
