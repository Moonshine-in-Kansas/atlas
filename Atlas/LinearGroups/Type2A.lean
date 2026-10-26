import Atlas.LinearGroups.Unitary.Family
import Atlas.LinearGroups.Unitary.Projective
import Atlas.LinearGroups.Unitary.ProjectiveOrder
import Atlas.FieldTheory.FiniteQuadraticExistence

/-! The constructive twisted type-A package for the actual Hermitian matrix quotient. -/
noncomputable section
namespace Atlas
universe u v
open Unitary

/-- All properties concern the retained SU matrix group and its actual center quotient. -/
structure Type2AConstruction (n : ℕ) (F K : Type*) [Field F] [Field K]
    [Finite F] [Finite K] [Algebra F K] (hdeg : Module.finrank F K = 2) (hn : 2 ≤ n) : Prop where
  finite : Finite (PSU F K n hdeg)
  simple : IsSimpleGroup (PSU F K n hdeg)
  nonabelian : ¬ IsMulCommutative (PSU F K n hdeg)
  order : Nat.card (PSU F K n hdeg) =
    (Nat.card F ^ (n*(n-1)/2) * ∏ i ∈ Finset.Icc 2 n, orderFactor (Nat.card F) i) /
      Nat.gcd n (Nat.card F+1)
  order_exact : Nat.card (PSU F K n hdeg) * Nat.gcd n (Nat.card F+1) = orderSU (Nat.card F) n
  special_order : Nat.card (SU F K n hdeg) = orderSU (Nat.card F) n
  full_center : Subgroup.center (SU F K n hdeg) = scalarSubgroup F K hdeg n
  center_order : Nat.card (Subgroup.center (SU F K n hdeg)) = Nat.gcd n (Nat.card F+1)
  generated : transvectionGenerated hdeg (n := n) = ⊤
  special_perfect : Group.IsPerfect (SU F K n hdeg)
  faithful : letI := isotropicAction hdeg (show 0 < n by omega)
    FaithfulSMul (PSU F K n hdeg) (IsotropicPoints F K n)
  primitive : letI := isotropicAction hdeg (show 0 < n by omega)
    MulAction.IsPreprimitive (PSU F K n hdeg) (IsotropicPoints F K n)
  points : Nat.card (IsotropicPoints F K n) =
    (orderFactor (Nat.card F) n * orderFactor (Nat.card F) (n-1)) / (Nat.card F^2-1)
  embedding_injective : Function.Injective (projectiveEmbedding hdeg (show 0 < n by omega))
  projection_onto : Function.Surjective (projection F K n hdeg)
  projection_kernel : (projection F K n hdeg).ker = Subgroup.center (SU F K n hdeg)
  determinant_onto : Function.Surjective (determinant hdeg (n := n))
  determinant_kernel : Nonempty (SU F K n hdeg ≃* (determinant hdeg (n := n)).ker)
  graph_field_involutive : Function.Involutive (graphFieldAutomorphism hdeg n)
  fixed_subgroup : Nonempty (SU F K n hdeg ≃* graphFieldFixed hdeg n)

theorem type2A_construction {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 2 ≤ n)
    (hg : Good n (Nat.card F)) : Type2AConstruction n F K hdeg hn := by
  have hn0 : 0 < n := by omega
  refine {
    finite := inferInstance
    simple := simple_of_good hdeg hg
    nonabelian := noncommutative_of_good hdeg hg
    order := card_psu_factor hdeg n hn0
    order_exact := card_psu_mul_gcd hdeg n hn0
    special_order := card_su hdeg n hn0
    full_center := center_eq_scalarSubgroup hdeg hn0
    center_order := card_center hdeg hn0
    generated := transvectionGenerated_eq_top_of_good hdeg hg
    special_perfect := special_perfect_of_good hdeg hg
    faithful := isotropicAction_faithful hdeg hn0
    primitive := isotropic_primitive hdeg hn
    points := ?_
    embedding_injective := projectiveEmbedding_injective hdeg hn0
    projection_onto := projection_surjective F K n hdeg
    projection_kernel := projection_kernel F K n hdeg
    determinant_onto := determinant_surjective hdeg hn0
    determinant_kernel := ⟨specialEquivDetKernel hdeg⟩
    graph_field_involutive := graphFieldAutomorphism_involutive hdeg n
    fixed_subgroup := ⟨specialUnitaryFixedEquiv hdeg n⟩ }
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn0
  simpa [Nat.add_comm] using card_isotropicPoints hdeg k

/-- Prime-power parameters produce the actual finite fields and retained matrix quotient. -/
theorem type2A_prime_power (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (hg : Good n (p^f)) :
    ∃ (F K : Type) (_ : Field F) (_ : Field K) (_ : Finite F) (_ : Finite K)
      (_ : Algebra F K) (hdeg : Module.finrank F K = 2),
      Nat.card F = p^f ∧ Nat.card K = p^(2*f) ∧ Type2AConstruction n F K hdeg hn := by
  obtain ⟨F,K,iF,iK,fF,fK,a,hF,hdeg,hK⟩ := FiniteQuadratic.exists_prime_power_quadratic p f hp hf
  letI := iF
  letI := iK
  letI := fF
  letI := fK
  letI := a
  refine ⟨F,K,iF,iK,fF,fK,a,hdeg,hF,hK, ?_⟩
  apply type2A_construction hdeg n hn
  simpa only [hF] using hg

/-- Group existence retains an explicit equivalence to the constructed center quotient. -/
theorem exists_type2A {F : Type u} {K : Type v} [Field F] [Field K] [Finite F] [Finite K]
    [Algebra F K] (hdeg : Module.finrank F K = 2) (n : ℕ) (hn : 2 ≤ n)
    (hg : Good n (Nat.card F)) :
    ∃ (G : Type v) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G = orderSU (Nat.card F) n / Nat.gcd n (Nat.card F+1) ∧
      Nonempty (G ≃* PSU F K n hdeg) ∧ Type2AConstruction n F K hdeg hn := by
  have h := type2A_construction hdeg n hn hg
  exact ⟨PSU F K n hdeg, inferInstance, h.finite, h.simple, h.nonabelian,
    card_psu hdeg n (by omega), ⟨MulEquiv.refl _⟩, h⟩
end Atlas
