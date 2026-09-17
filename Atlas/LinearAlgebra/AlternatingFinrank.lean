import Atlas.LinearAlgebra.SymplecticBasis

/-! # Even dimension of a nondegenerate alternating space, in every characteristic -/
noncomputable section
namespace Atlas.AlternatingForm
universe u v
variable {F : Type u} [Field F]

/-- Splitting off normalized alternating planes proves even dimension without
any restriction on the characteristic of the field. -/
theorem even_finrank {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate) :
    Even (Module.finrank F V) := by
  generalize hn : Module.finrank F V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hn0 : n = 0
    · simp [hn0]
    · haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) (by omega)
      obtain ⟨a,ha⟩ := exists_ne (0 : V)
      obtain ⟨b,hab⟩ := exists_partner B hB ha
      let P := complement B a b
      have hd := finrank_complement B hA a b hab
      have hlt : Module.finrank F P < n := by dsimp only [P]; omega
      have he := ih (Module.finrank F P) hlt (B.restrict P)
        (complement_alternating B hA a b hab)
        (complement_nondegenerate B hA a b hab hB) rfl
      obtain ⟨k,hk⟩ := he
      refine ⟨k + 1, ?_⟩
      dsimp only [P] at hk
      omega

/-- The dimension is twice an actual natural number. -/
theorem exists_half_finrank {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (hA : B.IsAlt) (hB : B.Nondegenerate) :
    ∃ n : ℕ, Module.finrank F V = 2 * n := by
  obtain ⟨n,hn⟩ := even_finrank B hA hB
  exact ⟨n,by omega⟩
end Atlas.AlternatingForm
