import Atlas.Lattices.EisensteinHexadVectors
import Atlas.Lattices.EisensteinClassCoordinates

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- All six heavy vectors on a constant hexad have the same theta-class. -/
theorem eisensteinHexadVector_class (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i j : Fin 12) :
    eisensteinClass (eisensteinHexadLatticeVector s hs i) =
      eisensteinClass (eisensteinHexadLatticeVector s hs j) := by
  let v : EisensteinCoordinates := fun k =>
    eisensteinTheta * ((if k=j then 1 else 0)-(if k=i then 1 else 0))
  apply (eisensteinClass_difference_three_iff _ _ v ?_).mpr
  · constructor
    · have he : eisensteinWordResidue v = 0 := by
        ext k
        simp [v,eisensteinWordResidue,
          show eisensteinResidue eisensteinTheta=0 by decide +kernel]
      rw [he]; exact Submodule.zero_mem _
    · have he : ∑ k,v k = 0 := by
        simp [v,← Finset.mul_sum,Finset.sum_sub_distrib]
      rw [he]; exact dvd_zero _
  · funext k
    change eisensteinTheta * ((if k ∈ s then 1 else 0)-(if k=i then 3 else 0)) -
      eisensteinTheta * ((if k ∈ s then 1 else 0)-(if k=j then 3 else 0)) = 3*v k
    dsimp [v]
    split_ifs <;> ring

/-- A two-coordinate glue vector needed to join the complementary hexads. -/
theorem eisenstein_twoPointGlue_mem (i j : Fin 12) :
    (fun k : Fin 12 => (1 : Eisenstein) - (if k=i then 3 else 0) -
      (if k=j then 3 else 0)) ∈ eisensteinLeechModule := by
  let u : EisensteinCoordinates := fun k =>
    eisensteinTheta*((if k=i then 1 else 0)+(if k=j then 1 else 0))
  refine ⟨1,u,?_,?_,?_⟩
  · intro k
    dsimp [u]
    split_ifs <;> simp [mul_add,← mul_assoc,← pow_two,eisensteinTheta_sq] <;> ring
  · have he : eisensteinWordResidue u = 0 := by
      ext k
      simp [u,eisensteinWordResidue,
        show eisensteinResidue eisensteinTheta=0 by decide +kernel]
    rw [he]; exact Submodule.zero_mem _
  · refine ⟨-eisensteinTheta,?_⟩
    simp only [Finset.sum_sub_distrib]
    simp
    linear_combination 3*eisensteinTheta_sq

/-- Complementary constant hexads give opposite theta-classes. -/
theorem eisensteinHexadVector_compl_class (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i j : Fin 12) :
    eisensteinClass (eisensteinHexadLatticeVector s hs i) =
      -eisensteinClass (eisensteinHexadLatticeVector sᶜ (ternaryConstantHexads_compl s hs) j) := by
  rw [← map_neg]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨⟨_,eisenstein_twoPointGlue_mem i j⟩,?_⟩
  apply Subtype.ext
  funext k
  change eisensteinTheta * (1-(if k=i then 3 else 0)-(if k=j then 3 else 0)) =
    eisensteinTheta*((if k ∈ s then 1 else 0)-(if k=i then 3 else 0)) -
      -(eisensteinTheta*((if k ∈ sᶜ then 1 else 0)-(if k=j then 3 else 0)))
  by_cases hk : k ∈ s <;> simp only [Finset.mem_compl,hk,not_true_eq_false,not_false_eq_true,
    ite_true,ite_false] <;> ring

end Atlas.Lattices
