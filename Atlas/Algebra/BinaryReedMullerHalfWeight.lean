import Atlas.Algebra.BinaryHalfWeight
import Atlas.Algebra.BinaryAffineFunctions

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

 theorem binaryAffineMonomial_mem (i : Fin 5) :
    (fun v => binaryAffineMonomials v i) ∈ binaryAffineCode := by
  classical
  refine ⟨Pi.single i 1,?_⟩
  funext v
  simp [binaryAffineEvaluation,Pi.single_apply,ite_mul]

 theorem binaryAffineMonomial_weight : ∀ i : Fin 5,
    4 ∣ hammingNorm (fun v => binaryAffineMonomials v i) := by decide +kernel

theorem binaryAffineCode_doublyEven (w : binaryAffineCode) : 4 ∣ hammingNorm w.val := by
  classical
  obtain ⟨c,hc⟩ := w.property
  have hmem (s : Finset (Fin 5)) :
      (∑ i ∈ s, c i • (fun v => binaryAffineMonomials v i)) ∈ binaryAffineCode :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (binaryAffineMonomial_mem i))
  have hs (s : Finset (Fin 5)) :
      4 ∣ hammingNorm (∑ i ∈ s, c i • (fun v => binaryAffineMonomials v i)) := by
    induction s using Finset.induction_on with
    | empty => simp [hammingNorm]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      refine doublyEven_add _ _ ?_ ih ?_
      · rcases bit_cases (c i) with h | h
        · simp [h,hammingNorm]
        · simpa [h] using binaryAffineMonomial_weight i
      · exact binaryQuadraticCode_le_affine_orthogonal
          (binaryAffineCode_le_quadratic (hmem s)) _
          (Submodule.smul_mem _ _ (binaryAffineMonomial_mem i))
  rw [← hc,binaryAffineEvaluation_sum]
  exact hs Finset.univ

theorem binaryQuadraticCode_even (w : binaryQuadraticCode) : 2 ∣ hammingNorm w.val := by
  have h1 : (fun _ : BinaryFour => (1 : Bit)) ∈ binaryAffineCode :=
    (binaryAffineCode_mem_iff _).mpr ⟨1,0,fun _ => (add_zero _).symm⟩
  have h := binaryQuadraticCode_le_affine_orthogonal w.property _ h1
  have hs : ∑ v, w.val v=0 := by simpa [binaryDot_apply] using h
  exact even_iff_two_dvd.mp ((even_weight_iff w.val).mpr hs)

noncomputable def binaryReedMullerHalfWeight : QuadraticMap Bit binaryQuadraticCode Bit :=
  binaryHalfWeightQuadratic binaryQuadraticCode binaryQuadraticCode_even

/-- The affine subcode is in the radical of the actual quadratic half-weight
form, so the form genuinely descends to quadratic functions modulo affine ones. -/
theorem binaryAffine_halfWeight_radical :
    binaryAffineCode.comap binaryQuadraticCode.subtype ≤ binaryReedMullerHalfWeight.radical := by
  intro w hw
  constructor
  · obtain ⟨k,hk⟩ := binaryAffineCode_doublyEven ⟨w.val,hw⟩
    change hammingNorm w.val=4*k at hk
    change ((hammingNorm w.val/2 : ℕ) : Bit)=0
    have he : hammingNorm w.val/2=2*k := by omega
    rw [he,Nat.cast_mul]
    simp
  · apply LinearMap.ext
    intro z
    rw [binaryReedMullerHalfWeight,binaryHalfWeightQuadratic_polar]
    exact binaryQuadraticCode_le_affine_orthogonal z.property _ hw

end Atlas.Algebra
