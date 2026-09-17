import Atlas.LinearGroups.Orthogonal.ElementaryQuotientOrder
import Atlas.LinearGroups.Orthogonal.ElementaryDerived
import Atlas.LinearGroups.Orthogonal.SpinorKernel

/-! # Identification of the actual elementary and intrinsic determinant/spinor kernels -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) (H : WittTwoFrame Q)
  (hQ : Q.polarBilin.Nondegenerate) (h2 : (2 : F) ≠ 0)

/-- The actual determinant and intrinsic spinor invariants together. -/
def determinantSpinor : isometrySubgroup Q →* rootsOfUnity 2 F × Atlas.SquareClass F :=
  (determinantSign Q hQ).prod (spinorNorm Q hQ h2)

theorem determinantSpinor_kernel : (determinantSpinor Q hQ h2).ker =
    specialSubgroup Q ⊓ (spinorNorm Q hQ h2).ker := by
  rw [determinantSpinor, MonoidHom.ker_prod, determinantSign_kernel]

include H in
theorem determinantSpinor_surjective : Function.Surjective (determinantSpinor Q hQ h2) := by
  rintro ⟨c, s⟩
  obtain ⟨t, ht⟩ := specialSpinorNorm_surjective Q hQ h2
    (fun x _ => ⟨H.e₁+x • H.f₁, frame_represents Q H x⟩) s
  have htt : determinant Q t.val = 1 := t.prop
  have hts : spinorNorm Q hQ h2 t.val = s := ht
  have hc : c.val.val^2 = (1 : F) := congrArg Units.val ((mem_rootsOfUnity 2 c.val).mp c.prop)
  rcases sq_eq_one_iff.mp hc with hc | hc
  · refine ⟨t.val, Prod.ext ?_ hts⟩
    apply Subtype.ext
    change determinant Q t.val = c.val
    rw [htt]
    exact Units.ext hc.symm
  · let a := H.e₁+(1 : F) • H.f₁
    have ha : Q a = 1 := frame_represents Q H 1
    have hane : Q a ≠ 0 := ne_of_eq_of_ne ha one_ne_zero
    let r := reflectionElement Q a hane
    refine ⟨r*t.val, Prod.ext ?_ ?_⟩
    · apply Subtype.ext
      change determinant Q (r*t.val) = c.val
      rw [map_mul, htt, mul_one, reflectionElement_determinant]
      exact Units.ext hc.symm
    · change spinorNorm Q hQ h2 (r*t.val) = s
      rw [map_mul, spinorNorm_reflection]
      have he : Units.mk0 (Q a) hane = 1 := Units.ext ha
      rw [he, map_one, one_mul, hts]

include H in
theorem determinantSpinor_kernel_index [Finite F] : (determinantSpinor Q hQ h2).ker.index = 4 := by
  have he := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (determinantSpinor Q hQ h2) (determinantSpinor_surjective Q H hQ h2)).toEquiv
  change Nat.card (_ ⧸ (determinantSpinor Q hQ h2).ker) = 4
  rw [he, Nat.card_prod, Atlas.card_squareOneUnits, Atlas.card_squareClass, if_neg h2]

include H hQ h2 in
/-- Over finite odd fields in Witt index ≥2, elementary equals the simultaneous intrinsic kernel. -/
theorem elementary_eq_intrinsicKernel [Finite F] : elementarySubgroup Q =
    specialSubgroup Q ⊓ (spinorNorm Q hQ h2).ker := by
  letI : Finite V := Finite.of_equiv (Fin (Module.finrank F V) → F)
    (Module.finBasis F V).equivFun.symm.toEquiv
  letI : Finite (isometrySubgroup Q) := Finite.of_injective
    (fun g : isometrySubgroup Q => (g.val : V → V))
    (fun x y h => Subtype.ext (DFunLike.coe_injective h))
  have hle : elementarySubgroup Q ≤ (determinantSpinor Q hQ h2).ker := by
    rw [determinantSpinor_kernel]
    exact elementary_le_special_spinor Q hQ h2
  have hupper : (elementarySubgroup Q).index ≤ 4 := card_elementaryQuotient_le_four Q H hQ h2
  have hindex := determinantSpinor_kernel_index Q H hQ h2
  have he : elementarySubgroup Q = (determinantSpinor Q hQ h2).ker := by
    by_contra hne
    have hlt := Subgroup.index_strictAnti (lt_of_le_of_ne hle hne)
    rw [hindex] at hlt
    omega
  exact he.trans (determinantSpinor_kernel Q hQ h2)

/-- Actual multiplicative equivalence to the previously counted restricted spinor kernel. -/
def elementarySpecialSpinorEquiv [Finite F] :
    elementarySubgroup Q ≃* specialSpinorKernel Q hQ h2 where
  toFun g := ⟨⟨g.val, ((elementary_eq_intrinsicKernel Q H hQ h2).le g.prop).1⟩,
    ((elementary_eq_intrinsicKernel Q H hQ h2).le g.prop).2⟩
  invFun g := ⟨g.val.val, (elementary_eq_intrinsicKernel Q H hQ h2).ge ⟨g.val.prop, g.prop⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Atlas.Orthogonal

