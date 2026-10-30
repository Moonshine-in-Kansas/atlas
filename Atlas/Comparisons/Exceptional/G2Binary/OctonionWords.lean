import Atlas.Comparisons.Exceptional.G2Binary.QuadraticTransitivity

/-!
ISO-6048 matching continuation, 27 October 2026. SOURCE ONLY, NOT CHECKED.

This four-letter alphabet is separate from the preserved three-letter
transitivity alphabet. Every letter is an actual octonion automorphism in H.
The fourth letter is the conjugate F(1) E(1) F(1)^(-1).
-/
namespace Atlas.Comparisons.G2Binary.Matching6048
open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit

def step4 (i : Fin 4) (x : V) : V :=
  ![rootAApply 1 x,
    weylRApply x,
    weylSApply (weylRApply (weylSApply x)),
    rootFApply 1 (rootEApply 1 (rootFApply (-1) x))] i

def element4 (i : Fin 4) : Automorphism K :=
  ![rootA 1,
    weylR,
    weylS * weylR * weylS⁻¹,
    rootF 1 * rootE 1 * (rootF 1)⁻¹] i

theorem element4_apply (i : Fin 4) (x : V) : (element4 i).val x = step4 i x := by
  fin_cases i <;>
    simp [element4, step4, rootA, rootAEquiv, rootALinear,
      weylR, weylREquiv, weylRLinear, weylS, weylSEquiv, weylSLinear,
      rootE, rootEEquiv, rootELinear, rootF, rootFEquiv, rootFLinear]

theorem element4_mem (i : Fin 4) : element4 i ∈ Atlas.G2.BinaryException.H := by
  fin_cases i
  · exact Atlas.G2.BinaryException.rootA_in_H 1
  · exact Atlas.G2.BinaryException.weylR_in_H
  · exact (inferInstance : Atlas.G2.BinaryException.H.Normal).conj_mem _
      Atlas.G2.BinaryException.weylR_in_H weylS
  · exact (inferInstance : Atlas.G2.BinaryException.H.Normal).conj_mem _
      (Atlas.G2.BinaryException.rootE_in_H 1) (rootF 1)

def act4 : List (Fin 4) → V → V
  | [], x => x
  | i :: w, x => step4 i (act4 w x)

def word4 : List (Fin 4) → Automorphism K
  | [] => 1
  | i :: w => element4 i * word4 w

theorem word4_apply (w : List (Fin 4)) (x : V) : (word4 w).val x = act4 w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (element4 i).val ((word4 w).val x) = _
    rw [ih, element4_apply]
    rfl

theorem word4_mem (w : List (Fin 4)) : word4 w ∈ Atlas.G2.BinaryException.H := by
  induction w with
  | nil => exact Atlas.G2.BinaryException.H.one_mem
  | cons i w ih => exact Atlas.G2.BinaryException.H.mul_mem (element4_mem i) ih

end Atlas.Comparisons.G2Binary.Matching6048
