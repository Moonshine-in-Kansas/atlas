import Atlas.LinearGroups.Orthogonal.ReflectionSquareClass
import Atlas.GroupTheory.TwoInvolutionsBound

/-! # The elementary quotient has at most four elements over a finite odd field -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

/-- The first actual hyperbolic plane represents every field value. -/
theorem frame_represents (c : F) : Q (H.e₁+c • H.f₁) = c := by
  rw [Atlas.Quadratic.add_smul, H.qe₁, H.qf₁, H.pair₁]
  ring

include H hQ h2 in
theorem card_elementaryQuotient_le_four [Finite F] : Nat.card (ElementaryQuotient Q) ≤ 4 := by
  have hcard : Nat.card (Atlas.SquareClass F) = 2 := by rw [Atlas.card_squareClass, if_neg h2]
  obtain ⟨s, t, hst, hcover⟩ := Nat.card_eq_two_iff.mp hcard
  obtain ⟨c, hc⟩ := Atlas.squareClass_surjective F s
  obtain ⟨d, hd⟩ := Atlas.squareClass_surjective F t
  let a := H.e₁+c.val • H.f₁
  let b := H.e₁+d.val • H.f₁
  have ha : Q a = c.val := frame_represents Q H c.val
  have hb : Q b = d.val := frame_represents Q H d.val
  have hane : Q a ≠ 0 := ne_of_eq_of_ne ha c.ne_zero
  have hbne : Q b ≠ 0 := ne_of_eq_of_ne hb d.ne_zero
  let r := elementaryProjection Q (reflectionElement Q a hane)
  let z := elementaryProjection Q (reflectionElement Q b hbne)
  have hra : Atlas.squareClass F (Units.mk0 (Q a) hane) = s := by
    have he : Units.mk0 (Q a) hane = c := Units.ext ha
    rw [he, hc]
  have hrb : Atlas.squareClass F (Units.mk0 (Q b) hbne) = t := by
    have he : Units.mk0 (Q b) hbne = d := Units.ext hb
    rw [he, hd]
  let S := Subgroup.closure ({r,z} : Set (ElementaryQuotient Q))
  have hr : reflectionSubgroup Q ≤ S.comap (elementaryProjection Q) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨v, hv, rfl⟩
    have hm : Atlas.squareClass F (Units.mk0 (Q v) hv) ∈ ({s,t} : Set (Atlas.SquareClass F)) := by
      rw [hcover]
      trivial
    rcases Set.mem_insert_iff.mp hm with he | he
    · have he' := elementaryProjection_reflection_squareClass Q H hQ h2 v a hv hane (he.trans hra.symm)
      change elementaryProjection Q (reflectionElement Q v hv) ∈ S
      rw [he']
      exact Subgroup.subset_closure (Set.mem_insert r {z})
    · have he := Set.mem_singleton_iff.mp he
      have he' := elementaryProjection_reflection_squareClass Q H hQ h2 v b hv hbne (he.trans hrb.symm)
      change elementaryProjection Q (reflectionElement Q v hv) ∈ S
      rw [he']
      exact Subgroup.subset_closure (Set.mem_insert_of_mem r (Set.mem_singleton z))
  rw [reflectionSubgroup_eq_top Q hQ h2] at hr
  have hgen : S = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (elementarySubgroup Q) x
    exact hr (Subgroup.mem_top g)
  have hrsq : r*r = 1 := by
    change elementaryProjection Q (reflectionElement Q a hane) * _ = 1
    rw [← map_mul, ← pow_two, reflectionElement_square, map_one]
  have hzsq : z*z = 1 := by
    change elementaryProjection Q (reflectionElement Q b hbne) * _ = 1
    rw [← map_mul, ← pow_two, reflectionElement_square, map_one]
  have hcomm := elementaryQuotient_isMulCommutative Q H hQ h2
  exact Atlas.card_le_four_of_two_commuting_involutions r z hrsq hzsq
    (isMulCommutative_iff.mp hcomm r z) hgen

end Atlas.Orthogonal
