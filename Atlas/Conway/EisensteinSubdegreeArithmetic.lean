import Atlas.Conway.EisensteinBlockArithmetic
import Mathlib.Algebra.BigOperators.Fin

namespace Atlas.Conway
open scoped BigOperators

def eisensteinSubdegree : Fin 13 → ℕ := Fin.cases 1 eisensteinNontrivialSubdegree

theorem eisensteinSubdegree_sum : (∑ i : Fin 13, eisensteinSubdegree i)=232960 := by
  rw [Fin.sum_univ_succ]
  change 1+(∑ i : Fin 12, eisensteinNontrivialSubdegree i)=232960
  decide +kernel

/-- Adjoin the distinguished singleton to the existing4096-subset arithmetic;
no additional enumeration of subsets of thirteen labels is used. -/
theorem eisensteinSubdegree_block_arithmetic (S : Finset (Fin 13)) (h0 : 0 ∈ S)
    (hd : (∑ i ∈ S,eisensteinSubdegree i) ∣ 232960) :
    (∑ i ∈ S,eisensteinSubdegree i)=1 ∨ (∑ i ∈ S,eisensteinSubdegree i)=232960 := by
  classical
  let T : Finset (Fin 12) := Finset.univ.filter (fun i => i.succ ∈ S)
  have hs : (∑ i ∈ S,eisensteinSubdegree i)=1+∑ i ∈ T,eisensteinNontrivialSubdegree i := by
    calc
      (∑ i ∈ S,eisensteinSubdegree i) =
          ∑ i : Fin 13, if i ∈ S then eisensteinSubdegree i else 0 := by simp
      _ = 1+∑ i ∈ T,eisensteinNontrivialSubdegree i := by
        rw [Fin.sum_univ_succ]
        simp [eisensteinSubdegree,h0,T,Finset.sum_filter]
  rw [hs] at hd ⊢
  rcases eisenstein_subdegree_block_arithmetic T hd with he|he
  · left; simp [he]
  · right; rw [he]
    decide +kernel

end Atlas.Conway
