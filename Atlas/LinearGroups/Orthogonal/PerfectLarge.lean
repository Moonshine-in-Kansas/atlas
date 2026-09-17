import Atlas.LinearGroups.Orthogonal.ElementaryTorus
import Atlas.LinearGroups.Symplectic.PerfectLarge
import Mathlib.GroupTheory.IsPerfect

/-! # Intrinsic orthogonal perfectness over odd fields of more than three elements -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
open scoped commutatorElement
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite F]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

include H hQ h2 in
theorem root_mem_elementary_commutator_of_scalar
    (e f : V) (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)
    (a : F) (ha : a ≠ 0) (ha₂ : a^2 ≠ 1) (w : complement Q e f) :
    rootComplementHom Q e f he (Multiplicative.ofAdd w) ∈
      ⁅elementarySubgroup Q, elementarySubgroup Q⁆ := by
  let c := a^2
  have hc : c ≠ 0 := pow_ne_zero 2 ha
  have hc₁ : c-1 ≠ 0 := sub_ne_zero.mpr ha₂
  let w' : complement Q e f := (c-1)⁻¹ • w
  let t := hyperbolicTorus Q e f he hf hef c hc
  let r := rootComplementHom Q e f he (Multiplicative.ofAdd w')
  have ht : t ∈ elementarySubgroup Q := squareTorus_mem_elementary Q H hQ h2 e f he hf hef a ha
  have hr : r ∈ elementarySubgroup Q := siegelElement_mem _ _ _ _ _
  have hcoef : c • w' + -w' = w := by
    dsimp [w']
    match_scalars <;> field_simp <;> ring
  have hcomm : ⁅t,r⁆ = rootComplementHom Q e f he (Multiplicative.ofAdd w) := by
    rw [commutatorElement_def]
    change (t*r*t⁻¹) * r⁻¹ = _
    rw [torus_root_conj Q e f he hf hef c hc w']
    change rootComplementHom Q e f he (Multiplicative.ofAdd (c • w')) *
      (rootComplementHom Q e f he (Multiplicative.ofAdd w'))⁻¹ = _
    rw [← map_inv, ← map_mul]
    congr 1
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator ht hr

include H hQ h2 in
theorem siegel_mem_elementary_commutator (hq : 3 < Nat.card F)
    (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) :
    siegelElement Q u v hu huv ∈ ⁅elementarySubgroup Q, elementarySubgroup Q⁆ := by
  by_cases hun : u = 0
  · subst u
    have he : siegelElement Q 0 v hu huv = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel Q 0 v x = x
      simp [siegel]
    rw [he]
    exact Subgroup.one_mem _
  · obtain ⟨f, hf, huf⟩ := exists_hyperbolic_partner Q u hu (fun h => hun (hQ.1 u h))
    obtain ⟨a, ha, ha₂⟩ := Atlas.Symplectic.exists_scalar_square_ne_one hq
    let w := rootPerpendicularRepresentative Q u f hu huf ⟨v, huv⟩
    have he := rootPerpendicularRepresentative_element Q u f hu huf ⟨v, huv⟩
    change rootComplementHom Q u f hu (Multiplicative.ofAdd w) = siegelElement Q u v hu huv at he
    rw [← he]
    exact root_mem_elementary_commutator_of_scalar Q H hQ h2 u f hu hf huf a ha ha₂ w

include H hQ h2 in
/-- Perfectness of the actual elementary group, independent of projective simplicity. -/
theorem elementary_perfect_of_card_gt_three (hq : 3 < Nat.card F) :
    Group.IsPerfect (elementarySubgroup Q) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_left _ _) _
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  exact siegel_mem_elementary_commutator Q H hQ h2 hq u v hu huv

end Atlas.Orthogonal
