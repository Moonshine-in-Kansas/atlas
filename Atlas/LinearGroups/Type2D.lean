import Atlas.LinearGroups.Orthogonal.Minus.Family
import Atlas.FieldTheory.FiniteQuadraticExistence

/-! Constructive stable twisted type-D package for the actual norm-tail quadratic space.
This package covers half-dimension n≥4; order separately covers n≥3.
No low-rank comparison or graph-field characterization is asserted here. -/
noncomputable section
namespace Atlas
universe u v
open Orthogonal Orthogonal.Minus

/-- All fields refer to the same quadratic space, intrinsic elementary kernel and scalar quotient. -/
structure Type2DConstruction (n : ℕ) (F K : Type*) [Field F] [Field K]
    [Finite F] [Finite K] [Algebra F K] (hdeg : Module.finrank F K = 2) : Prop where
  finite : Finite (Orthogonal.DMinus n F K hdeg)
  simple : IsSimpleGroup (Orthogonal.DMinus n F K hdeg)
  nonabelian : ¬ IsMulCommutative (Orthogonal.DMinus n F K hdeg)
  order : Nat.card (Orthogonal.DMinus n F K hdeg) = orderNumerator (Nat.card F) n /
    Nat.gcd 4 (Nat.card F^n+1)
  full_order : Nat.card (O hdeg (n-1)) = 2 * orderNumerator (Nat.card F) n
  elementary_perfect : Group.IsPerfect (E hdeg (n-1))
  full_center : elementaryScalarSubgroup (form hdeg (n-1)) =
    Subgroup.center (E hdeg (n-1))
  faithful : FaithfulSMul (Orthogonal.DMinus n F K hdeg)
    (SingularPoints (form hdeg (n-1)))
  primitive : MulAction.IsPreprimitive (Orthogonal.DMinus n F K hdeg)
    (SingularPoints (form hdeg (n-1)))
  projection_onto : Function.Surjective (projectiveElementaryMap (form hdeg (n-1)))
  projection_kernel : (projectiveElementaryMap (form hdeg (n-1))).ker =
    Subgroup.center (E hdeg (n-1))
  intrinsic_odd : ∀ (h2 : (2 : F) ≠ 0) (g : O hdeg (n-1)),
    g ∈ E hdeg (n-1) ↔ determinant (form hdeg (n-1)) g = 1 ∧
      spinorNorm (form hdeg (n-1)) (polar_nondegenerate hdeg _) h2 g = 1
  intrinsic_even : ∀ (_ : CharP F 2) (g : O hdeg (n-1)),
    g ∈ E hdeg (n-1) ↔ dicksonValue (form hdeg (n-1)) g = 0

theorem type2D_construction {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 4 ≤ n) :
    Type2DConstruction n F K hdeg := by
  refine {
    finite := inferInstance
    simple := family_simple hdeg n hn
    nonabelian := family_noncommutative hdeg n hn
    order := family_order hdeg n (by omega)
    full_order := family_full_order hdeg n (by omega)
    elementary_perfect := family_elementary_perfect hdeg n hn
    full_center := family_center_scalar hdeg n (by omega)
    faithful := family_faithful hdeg n (by omega)
    primitive := family_primitive hdeg n hn
    projection_onto := projectiveElementaryMap_surjective _
    projection_kernel := family_projection_kernel hdeg n (by omega)
    intrinsic_odd := family_intrinsic_odd hdeg n (by omega)
    intrinsic_even := ?_ }
  intro hchar g
  let := hchar
  exact family_intrinsic_even hdeg n (by omega) g

/-- Every prime power supplies actual finite fields and the stable nonsplit family. -/
theorem type2D_prime_power (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hn : 4 ≤ n) :
    ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K)
      (_ : Algebra F K) (hdeg : Module.finrank F K = 2),
      Nat.card F = p^f ∧ Nat.card K = p^(2*f) ∧ Type2DConstruction n F K hdeg := by
  obtain ⟨F,K,iF,iK,fF,fK,a,hF,hdeg,hK⟩ := FiniteQuadratic.exists_prime_power_quadratic p f hp hf
  let := iF
  let := iK
  let := fF
  let := fK
  let := a
  exact ⟨F,K,iF,iK,fF,fK,a,hdeg,hF,hK,type2D_construction hdeg n hn⟩

/-- Group existence retains an explicit equivalence with the actual norm-tail quotient. -/
theorem exists_type2D {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 4 ≤ n) :
    ∃ (G : Type (max u v)) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
      ¬ IsMulCommutative G ∧ Nat.card G = orderNumerator (Nat.card F) n /
        Nat.gcd 4 (Nat.card F^n+1) ∧ Nonempty (G ≃* Orthogonal.DMinus n F K hdeg) ∧
      Type2DConstruction n F K hdeg := by
  have h := type2D_construction hdeg n hn
  exact ⟨Orthogonal.DMinus n F K hdeg,inferInstance,h.finite,h.simple,
    h.nonabelian,h.order,⟨MulEquiv.refl _⟩,h⟩

end Atlas

