import Atlas.Rudvalis.BinaryTranslations

/-! Coordinate symmetries preserve the actual orthogonal torsion code. -/
namespace Atlas.Rudvalis
open scoped BigOperators

theorem binaryPermutation_torsion (g : binaryPermutationGroup) (b : BinaryWord)
    (hb : b∈binaryTorsion) : b ∘ g.val∈binaryTorsion := by
  intro d hd
  have hh := hb (d ∘ g.val.symm) ((g⁻¹).prop d |>.mp hd)
  rw [Atlas.Codes.binaryDot_apply] at hh ⊢
  have he := Equiv.sum_comp g.val (fun i => d (g.val.symm i)*b i)
  simpa [Function.comp_def] using he.trans hh

end Atlas.Rudvalis
