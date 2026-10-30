import Atlas.Comparisons.Exceptional.G2Binary.QuadraticFaithful
import Atlas.LinearGroups.G2.BinarySign

/-! A marked transitive 28-point geometry. The certificate consists of 28
root words of length at most seven; each is checked on actual octonion vectors.
No enumeration of group elements or abstract permutation model is used. -/
namespace Atlas.Comparisons.G2Binary
open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit

def baseVector : V := ![1,0,0,0,1,0,0,1]
def basePoint : QuadraticPoint := ⟨baseVector,by decide⟩

def step (i : Fin 3) (x : V) : V :=
  ![rootAApply 1 x, weylRApply x, weylSApply (weylRApply (weylSApply x))] i

def stepElement (i : Fin 3) : Automorphism K :=
  ![rootA 1, weylR, weylS * weylR * weylS⁻¹] i

theorem stepElement_apply (i : Fin 3) (x : V) : (stepElement i).val x = step i x := by
  fin_cases i <;> simp [stepElement,step,rootA,rootAEquiv,rootALinear,
    weylR,weylREquiv,weylRLinear,weylS,weylSEquiv,weylSLinear]

theorem stepElement_mem (i : Fin 3) : stepElement i ∈ BinaryException.H := by
  fin_cases i
  · exact BinaryException.rootA_in_H 1
  · exact BinaryException.weylR_in_H
  · exact (inferInstance : BinaryException.H.Normal).conj_mem _
      BinaryException.weylR_in_H weylS

def wordAction : List (Fin 3) → V → V
  | [],x => x
  | i::w,x => step i (wordAction w x)

def wordElement : List (Fin 3) → Automorphism K
  | [] => 1
  | i::w => stepElement i * wordElement w

theorem wordElement_apply (w : List (Fin 3)) (x : V) :
    (wordElement w).val x = wordAction w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (stepElement i).val ((wordElement w).val x) = _
    rw [ih,stepElement_apply]
    rfl

theorem wordElement_mem (w : List (Fin 3)) : wordElement w ∈ BinaryException.H := by
  induction w with
  | nil => exact BinaryException.H.one_mem
  | cons i w ih => exact BinaryException.H.mul_mem (stepElement_mem i) ih

def markedVector (i : Fin 28) : V :=
  ![![0,0,1,0,1,1,0,0],
    ![0,0,1,0,1,1,0,1],
    ![0,0,1,0,1,1,1,0],
    ![0,0,1,0,1,1,1,1],
    ![0,1,0,0,1,0,1,0],
    ![0,1,0,0,1,0,1,1],
    ![0,1,0,0,1,1,1,0],
    ![0,1,0,0,1,1,1,1],
    ![0,1,1,0,1,0,1,0],
    ![0,1,1,0,1,0,1,1],
    ![0,1,1,0,1,1,0,0],
    ![0,1,1,0,1,1,0,1],
    ![1,0,0,0,1,0,0,1],
    ![1,0,0,0,1,0,1,1],
    ![1,0,0,0,1,1,0,1],
    ![1,0,0,0,1,1,1,1],
    ![1,0,1,0,1,0,0,1],
    ![1,0,1,0,1,0,1,1],
    ![1,0,1,0,1,1,0,0],
    ![1,0,1,0,1,1,1,0],
    ![1,1,0,0,1,0,0,1],
    ![1,1,0,0,1,0,1,0],
    ![1,1,0,0,1,1,0,1],
    ![1,1,0,0,1,1,1,0],
    ![1,1,1,0,1,0,0,1],
    ![1,1,1,0,1,0,1,0],
    ![1,1,1,0,1,1,0,0],
    ![1,1,1,0,1,1,1,1]] i
def markedWord (i : Fin 28) : List (Fin 3) :=
  ![[2],
    [2,1,0],
    [1,2,0,1,2],
    [1,2,0,1,2,0],
    [1,2],
    [1,2,1,0],
    [2,0,1,2],
    [2,0,1,2,0],
    [1,2,0],
    [1,2,0,1,0],
    [2,0],
    [2,0,1,0],
    [],
    [0,1,2,1,0],
    [2,1,0,1,2],
    [0,2,0,1,2,0],
    [1,0],
    [0,1,2,0,1,0],
    [1,0,1,2],
    [1,0,2,0,1,2],
    [0],
    [0,1,2],
    [2,1,0,1,2,0],
    [0,2,0,1,2],
    [0,1,0],
    [0,1,2,0],
    [1,0,1,2,0],
    [0,1,2,0,1,2,0]] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Exhaust the 256 algebra vectors and check the 28 short root words.
theorem marking_complete :
    (∀ i : Fin 28, IsQuadraticRoot (markedVector i) ∧ markedVector i 3 = 0) ∧
    (∀ x : V, IsQuadraticRoot x ∧ x 3 = 0 → ∃ i : Fin 28, markedVector i = x) ∧
    (∀ i : Fin 28, wordAction (markedWord i) baseVector = markedVector i) := by decide

theorem exists_word_to_point (x : QuadraticPoint) :
    ∃ w : List (Fin 3), (wordElement w) • basePoint = x := by
  obtain ⟨i,hi⟩ := marking_complete.2.1 x.val x.property
  refine ⟨markedWord i,?_⟩
  apply Subtype.ext
  change normalize ((wordElement (markedWord i)).val baseVector) = x.val
  rw [wordElement_apply,marking_complete.2.2,hi]
  simp [normalize,x.property.2]

instance longRoot_quadraticPoint_transitive :
    MulAction.IsPretransitive BinaryException.H QuadraticPoint where
  exists_smul_eq x y := by
    obtain ⟨u,hu⟩ := exists_word_to_point x
    obtain ⟨v,hv⟩ := exists_word_to_point y
    refine ⟨⟨wordElement v * (wordElement u)⁻¹,
      BinaryException.H.mul_mem (wordElement_mem v)
        (BinaryException.H.inv_mem (wordElement_mem u))⟩,?_⟩
    change (wordElement v * (wordElement u)⁻¹) • x = y
    rw [← hu,SemigroupAction.mul_smul,inv_smul_smul,hv]

end Atlas.Comparisons.G2Binary
