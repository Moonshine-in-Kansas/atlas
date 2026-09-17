import Atlas.Fischer.OctadicWordEigenvectors
import Atlas.Fischer.DuadCharacterDecomposition

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octadicRoot_rational_word_expansion {O : Octad} (Q : OctadCalibration O)
    (χ : OctadicCharacter O) : octadicRoot Q χ=(1/2 : ℚ) •
      ∑ b : octadShortenedCode O, rationalBitSign (χ b) • octadicWordTerm Q b := by
  rw [octadicRoot_word_expansion]
  simp only [rationalBitSign_smul_scalar]
  have h : (1/2 : Scalar)=((1/2 : ℚ) : Scalar) := by norm_num
  rw [h,Rat.cast_smul_eq_qsmul]

/-- Exact unique-decomposition isolation of each rational product coordinate.
No magnitude or sign for the remaining single term is presumed. -/
theorem duadWordPair_coordinate_isolation {F G : Octad}
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G)
    (b : octadShortenedCode F) (c : octadShortenedCode G) (p : RationalCoordinateIndex)
    (hp : rationalCoordinateGolayWord p=b.val+c.val) :
    rationalCoordinateEquiv (product (octadicRoot Q χ) (octadicRoot R ψ)) p=
      (1/4 : ℚ)*rationalBitSign (χ b)*rationalBitSign (ψ c)*
        rationalCoordinateEquiv (product (octadicWordTerm Q b) (octadicWordTerm R c)) p := by
  have hz (u : octadShortenedCode F) (v : octadShortenedCode G) (hn : ¬(u=b ∧ v=c)) :
      rationalCoordinateEquiv (product (octadicWordTerm Q u) (octadicWordTerm R v)) p=0 := by
    apply (golayCommonEigenvector_iff _ _).mp (octadicWordTerm_product_eigenvector Q R u v) p
    intro he
    have hs : u.val+v.val=b.val+c.val := he.symm.trans hp
    have heq := (duadOctadSumEquiv (F.val ∩ G.val) hFG F G rfl).injective
      (show duadOctadSumEquiv _ hFG F G rfl (u,v)=duadOctadSumEquiv _ hFG F G rfl (b,c) from
        Subtype.ext hs)
    exact hn ⟨congrArg Prod.fst heq,congrArg Prod.snd heq⟩
  rw [octadicRoot_rational_word_expansion Q,octadicRoot_rational_word_expansion R,
    product_rat_smul_left,product_rat_smul_right]
  simp only [product_sum_left,product_sum_right,product_rat_smul_left,product_rat_smul_right,
    map_smul,map_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single c]
  · rw [Finset.sum_eq_single b]
    · ring
    · intro u _ hu
      rw [hz u c (fun h => hu h.1),mul_zero]
    · intro h
      exact (h (Finset.mem_univ b)).elim
  · intro v _ hv
    have hs : (∑ u : octadShortenedCode F, rationalBitSign (χ u)*
        rationalCoordinateEquiv (product (octadicWordTerm Q u) (octadicWordTerm R v)) p)=0 := by
      apply Finset.sum_eq_zero
      intro u _
      rw [hz u v (fun h => hv h.2),mul_zero]
    rw [hs,mul_zero]
  · intro h
    exact (h (Finset.mem_univ c)).elim

end Atlas.Fischer
