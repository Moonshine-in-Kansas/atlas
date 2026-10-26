import Atlas.LinearGroups.ReeF4.TorusCubicSupport

/-! Cubic polynomial preservation by the actual two-parameter diagonal action.
The proof matches each of the 32 triple-trace monomials with its character. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [CharP F 2]

theorem torusTripleTrace (m : ℕ) (a b : Fˣ)
    (x y z : SplitOctonion.Carrier F) :
    SplitOctonion.trace (SplitOctonion.mul
      (SplitOctonion.mul
        (fun j => (torusWeight (G := Fˣ) m a b (0,j) : F) * x j)
        (fun j => (torusWeight (G := Fˣ) m a b (1,j) : F) * y j))
        (fun j => (torusWeight (G := Fˣ) m a b (2,j) : F) * z j)) =
      SplitOctonion.trace (SplitOctonion.mul (SplitOctonion.mul x y) z) := by
  rw [octonionTripleTrace_eq_sum, octonionTripleTrace_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hw := congrArg (fun u : Fˣ => (u : F)) (torusCubicTriple_weight m a b i)
  simp only [Units.val_mul, Units.val_one] at hw
  calc
    _ = ((torusWeight (G := Fˣ) m a b (0,(cubicTripleIndices i).1) : F) *
        (torusWeight (G := Fˣ) m a b (1,(cubicTripleIndices i).2.1) : F) *
        (torusWeight (G := Fˣ) m a b (2,(cubicTripleIndices i).2.2) : F)) *
        (x (cubicTripleIndices i).1 * y (cubicTripleIndices i).2.1 *
          z (cubicTripleIndices i).2.2) := by ring
    _ = _ := by rw [hw, one_mul]

theorem torusFormula_cubic (m : ℕ) (a b : Fˣ) (w : Carrier F) :
    Albert.norm (rootDiagonalFormula (torusWeight (G := Fˣ) m a b) w) = Albert.norm w := by
  simp only [Albert.norm, rootDiagonalFormula, torusBlock_norm, torusTripleTrace]

theorem torusEquiv_cubic (m : ℕ) (a b : Fˣ) (w : TraceZero F) :
    traceZeroCubic (torusEquiv m a b w) = traceZeroCubic w :=
  torusFormula_cubic m a b w.val

end Atlas.ReeF4
