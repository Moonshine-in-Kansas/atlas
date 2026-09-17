import Atlas.Codes.TernaryGolayFullWeight

namespace Atlas.Codes
open scoped BigOperators

def ternaryConstantParameters : Fin 6 → TernaryParameters :=
  ![![1,1,0,0,0,0], ![0,1,1,0,0,0], ![1,1,0,1,0,0],
    ![0,0,1,1,0,0], ![1,0,0,0,1,0], ![0,0,0,0,0,1]]

def ternaryConstantGenerator (k : Fin 6) : TernaryWord :=
  ternaryEncoder (ternaryConstantParameters k)

def ternaryConstantInverse : Fin 6 → Fin 6 → ZMod 3 :=
  ![![2,2,2,1,0,0], ![2,1,1,2,0,0], ![1,0,2,1,0,0],
    ![2,0,1,0,0,0], ![1,1,1,2,1,0], ![0,0,0,0,0,1]]

theorem ternaryConstantGenerator_mem (k : Fin 6) :
    ternaryConstantGenerator k ∈ ternaryGolay := ⟨_, rfl⟩

theorem ternaryConstantGenerator_spec : ∀ k : Fin 6,
    ternaryWeight (ternaryConstantGenerator k) = 6 ∧
      ∀ i, ternaryConstantGenerator k i = 0 ∨ ternaryConstantGenerator k i = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- This checks only the 729 six-dimensional parameter vectors over F3.
theorem ternaryConstantGenerator_decompose : ∀ p : TernaryParameters,
    ternaryEncoder p = ∑ j : Fin 6, p j •
      ∑ k : Fin 6, ternaryConstantInverse j k • ternaryConstantGenerator k := by
  decide +kernel

theorem ternaryConstantGenerator_span :
    Submodule.span (ZMod 3) (Set.range ternaryConstantGenerator) = ternaryGolay := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨k,rfl⟩; exact ternaryConstantGenerator_mem k)
  · rintro _ ⟨p,rfl⟩
    rw [ternaryConstantGenerator_decompose p]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩)

end Atlas.Codes
