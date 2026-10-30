import Atlas.GroupTheory.OrderedSubgroupCollection

/-!
Source-only generic helpers for the tail normalizer repair. No Ree or Albert
module is imported. The range argument, finite join bound, and involution
cancellation are proved with an abstract ambient group.
No compiler, checker, audit or memory measurement was run for this candidate.
-/

namespace Atlas.GroupTheory.TailNormalizer

variable {G : Type*} [Group G]

/-- Surjective parameters suffice to bound the image of a whole homomorphism
range under conjugation. All range elimination takes place in this generic lemma. -/
theorem range_le_conj_comap_of_surjective_parameters
    {A T : Type*} [Group A] (H : Subgroup G) (x : G)
    (f : A →* G) (p : T → A) (hp : Function.Surjective p) (q : T → G)
    (hconj : ∀ t, x * f (p t) * x⁻¹ = q t)
    (hq : ∀ t, q t ∈ H) :
    f.range ≤ H.comap (MulAut.conj x).toMonoidHom := by
  rintro y ⟨a, rfl⟩
  obtain ⟨t, rfl⟩ := hp a
  change x * f (p t) * x⁻¹ ∈ H
  rw [hconj t]
  exact hq t

/-- The seven inclusions are combined without list-membership case analysis.
The definition of the join is unfolded only on a literal list of abstract subgroups. -/
theorem subgroupListJoin_seven_le
    (H₀ H₁ H₂ H₃ H₄ H₅ H₆ K : Subgroup G)
    (h₀ : H₀ ≤ K) (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K) (h₃ : H₃ ≤ K)
    (h₄ : H₄ ≤ K) (h₅ : H₅ ≤ K) (h₆ : H₆ ≤ K) :
    subgroupListJoin [H₀, H₁, H₂, H₃, H₄, H₅, H₆] ≤ K :=
  sup_le h₀ (sup_le h₁ (sup_le h₂ (sup_le h₃
    (sup_le h₄ (sup_le h₅ (sup_le h₆ bot_le))))))

/-- Expose conjugation membership from the comap bound in the abstract group. -/
theorem conjugate_mem_of_le_conj_comap (H : Subgroup G) (x : G)
    (hle : H ≤ H.comap (MulAut.conj x).toMonoidHom)
    {g : G} (hg : g ∈ H) : x * g * x⁻¹ ∈ H :=
  hle hg

/-- For an involution, the reverse normalizer implication follows from the same
forward conjugation inclusion. No finiteness or cardinality is required. -/
theorem mem_normalizer_of_inv_eq_self_of_conjugate_mem
    (H : Subgroup G) (x : G) (hx : x⁻¹ = x)
    (hc : ∀ g ∈ H, x * g * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer H := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact hc g
  · intro hg
    have hh := hc (x * g * x⁻¹) hg
    have he : x * (x * g * x⁻¹) * x⁻¹ = g := by
      calc
        _ = x⁻¹ * (x * g * x⁻¹) * x := by rw [hx]
        _ = g := by
          simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    exact he ▸ hh

end Atlas.GroupTheory.TailNormalizer
