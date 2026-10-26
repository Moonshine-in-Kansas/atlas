import Atlas.Comparisons.Exceptional.E6.RootReduction
import Mathlib.LinearAlgebra.StdBasis

/-! The binary reduction kernel of integral isometries is contained in {1,-1}.
The later Weyl-group discriminant argument must exclude the negative scalar. -/
namespace Atlas.Comparisons.E6Lattice

def simpleRoot (i : Fin 6) : Fin 6 → ℤ := Pi.single i 1

theorem simpleRoot_norm (i : Fin 6) : norm (simpleRoot i) = 1 := by
  revert i
  decide

theorem norm_parallelogram (x y : Fin 6 → ℤ) :
    norm (x+y) + norm (x-y) = 2*norm x + 2*norm y := by
  simp [norm]
  ring

variable (f : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 6 → ℤ))
    (hf : ∀ x, norm (f x) = norm x)
    (hred : ∀ x, reduceBinary (f x) = reduceBinary x)

include hf hred

theorem simpleRoot_image_sign (i : Fin 6) :
    f (simpleRoot i) = simpleRoot i ∨ f (simpleRoot i) = -simpleRoot i :=
  root_reduction_pair _ _ (simpleRoot_norm i)
    ((hf _).trans (simpleRoot_norm i)) (hred _).symm

theorem fixes_adjacent (i j : Fin 6)
    (hij : norm (simpleRoot i + simpleRoot j) = 1)
    (hi : f (simpleRoot i) = simpleRoot i) : f (simpleRoot j) = simpleRoot j := by
  rcases simpleRoot_image_sign f hf hred j with hj | hj
  · exact hj
  · have he := hf (simpleRoot i + simpleRoot j)
    rw [map_add,hi,hj,← sub_eq_add_neg,hij] at he
    have hp := norm_parallelogram (simpleRoot i) (simpleRoot j)
    rw [hij,he,simpleRoot_norm,simpleRoot_norm] at hp
    omega

theorem eq_id_of_fixes_first (h0 : f (simpleRoot 0) = simpleRoot 0) :
    f = LinearMap.id := by
  have h1 := fixes_adjacent f hf hred 0 1 (by decide) h0
  have h2 := fixes_adjacent f hf hred 1 2 (by decide) h1
  have h3 := fixes_adjacent f hf hred 2 3 (by decide) h2
  have h4 := fixes_adjacent f hf hred 3 4 (by decide) h3
  have h5 := fixes_adjacent f hf hred 2 5 (by decide) h2
  apply (Pi.basisFun ℤ (Fin 6)).ext
  intro i
  simp only [Pi.basisFun_apply,LinearMap.id_apply]
  change f (simpleRoot i) = simpleRoot i
  fin_cases i <;> assumption

theorem binary_kernel_scalar : f = LinearMap.id ∨ f = -LinearMap.id := by
  rcases simpleRoot_image_sign f hf hred 0 with h | h
  · exact Or.inl (eq_id_of_fixes_first f hf hred h)
  · right
    have hn : ∀ x, norm ((-f) x) = norm x := by
      intro x
      simpa only [LinearMap.neg_apply,norm_neg] using hf x
    have hr : ∀ x, reduceBinary ((-f) x) = reduceBinary x := by
      intro x
      have he := hred x
      funext i
      have he' := congrFun he i
      simpa only [reduceBinary,LinearMap.neg_apply,Pi.neg_apply,
        Int.cast_neg,ZMod.neg_eq_self_mod_two] using he'
    have h0 : (-f) (simpleRoot 0) = simpleRoot 0 := by simp [h]
    have he := eq_id_of_fixes_first (-f) hn hr h0
    exact neg_injective (by simpa using he)

end Atlas.Comparisons.E6Lattice
