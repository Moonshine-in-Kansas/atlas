import Atlas.LinearGroups.Orthogonal.DStructureAllChar
import Atlas.LinearGroups.Orthogonal.DFamily
import Atlas.LinearGroups.Orthogonal.SimplicityAllCharD
import Atlas.LinearGroups.Orthogonal.EvenDDerived
import Mathlib.FieldTheory.Finite.GaloisField

/-! # The public constructive split-D family, in rank at least four

The witness is the actual quadratic-form scalar quotient. Its singular-point
action, elementary cover, derived-subgroup identity and scalar center remain
visible in the package; order and simplicity have separate supporting roots.
-/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F]

theorem DPlus_simple (n : ℕ) (hn : 4 ≤ n) : IsSimpleGroup (DPlus n F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  exact projectiveD_simple_all_char k

theorem DPlus_noncommutative (n : ℕ) (hn : 4 ≤ n) : ¬ IsMulCommutative (DPlus n F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  exact projectiveD_noncommutative_all_char k

theorem DPlus_perfect (n : ℕ) (hn : 4 ≤ n) : Group.IsPerfect (DPlus n F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  exact projectiveD_perfect_all_char k

theorem DPlus_elementary_perfect (n : ℕ) (hn : 4 ≤ n) :
    Group.IsPerfect (elementarySubgroup (formD n F)) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  exact elementaryD_perfect_all_char k

theorem DPlus_faithful (n : ℕ) (hn : 4 ≤ n) :
    FaithfulSMul (DPlus n F) (SingularPoints (formD n F)) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact projectiveSingularD_faithful k

theorem DPlus_primitive (n : ℕ) (hn : 4 ≤ n) :
    MulAction.IsPreprimitive (DPlus n F) (SingularPoints (formD n F)) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  exact projectiveSingularD_primitive k

theorem DPlus_transitive (n : ℕ) (hn : 4 ≤ n) :
    MulAction.IsPretransitive (DPlus n F) (SingularPoints (formD n F)) := by
  letI := DPlus_primitive (F := F) n hn
  infer_instance

theorem DPlus_scalar_eq_center (n : ℕ) (hn : 4 ≤ n) :
    elementaryScalarSubgroup (formD n F) = Subgroup.center (elementarySubgroup (formD n F)) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact elementaryScalarSubgroup_eq_center _ (wittTwoFrameD k) polarD_nondegenerate

theorem DPlus_roots_normal_generate (n : ℕ) (hn : 4 ≤ n)
    (p : SingularPoints (formD n F)) :
    Subgroup.normalClosure (projectiveRootSubgroup (formD n F) p : Set (DPlus n F)) = ⊤ := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact projectiveRootD_normalClosure_eq_top k p

variable [Finite F]

/-- Exact public simplicity range: every advertised rank and every finite field is admissible. -/
theorem DPlus_simple_iff (n : ℕ) (hn : 4 ≤ n) :
    IsSimpleGroup (DPlus n F) ↔ DPlus_admissible n (Nat.card F) := by
  constructor
  · intro _
    exact ⟨hn,by have h := Finite.one_lt_card (α := F); omega⟩
  · intro _
    exact DPlus_simple n hn

/-- The public elementary cover is the intrinsic derived subgroup in all finite characteristics. -/
theorem DPlus_elementary_eq_derived (n : ℕ) (hn : 4 ≤ n) :
    elementarySubgroup (formD n F) = commutator (O_DPlus n F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact elementaryD_eq_commutator_even k
  · exact elementaryD_eq_commutator (k + 1) h2
/-- Independent order of the actual full orthogonal carrier. -/
theorem DPlus_full_order (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (O_DPlus n F) = 2 * DPlus_order_numerator n (Nat.card F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  have h := card_fullD (F := F) (k + 2)
  simpa only [DPlus_order_numerator,show k + 3 - 1 = k + 2 by omega, mul_assoc] using h

theorem DPlus_elementary_order_exact (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (elementarySubgroup (formD n F)) * Nat.gcd 2 (Nat.card F - 1) =
      DPlus_order_numerator n (Nat.card F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  simpa only [DPlus_order_numerator,show k + 3 - 1 = k + 2 by omega]
    using card_elementaryD_all_char_mul_gcd_two (F := F) k

theorem DPlus_elementary_order (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (elementarySubgroup (formD n F)) =
      DPlus_order_numerator n (Nat.card F) / Nat.gcd 2 (Nat.card F - 1) := by
  rw [← DPlus_elementary_order_exact n hn,
    Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 2))]

theorem DPlus_elementary_index (n : ℕ) (hn : 4 ≤ n) :
    (elementarySubgroup (formD n F)).index = 2 * Nat.gcd 2 (Nat.card F - 1) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  exact elementaryD_index_all_char k

theorem DPlus_center_order_exact (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (Subgroup.center (elementarySubgroup (formD n F))) * Nat.gcd 2 (Nat.card F - 1) =
      DPlus_order_denominator n (Nat.card F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  exact card_elementaryD_center_all_char_mul_gcd_two k

theorem DPlus_scalar_order_exact (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (elementaryScalarSubgroup (formD n F)) * Nat.gcd 2 (Nat.card F - 1) =
      DPlus_order_denominator n (Nat.card F) := by
  rw [DPlus_scalar_eq_center n hn]
  exact DPlus_center_order_exact n hn

theorem DPlus_center_order (n : ℕ) (hn : 4 ≤ n) :
    Nat.card (Subgroup.center (elementarySubgroup (formD n F))) =
      DPlus_order_denominator n (Nat.card F) / Nat.gcd 2 (Nat.card F - 1) := by
  rw [← DPlus_center_order_exact n hn,
    Nat.mul_div_cancel _ (Nat.gcd_pos_of_pos_left _ (by decide : 0 < 2))]

/-- Odd-characteristic Omega is the simultaneous determinant and spinor kernel. -/
theorem DPlus_odd_intrinsic (n : ℕ) (hn : 4 ≤ n) (h2 : (2 : F) ≠ 0) :
    elementarySubgroup (formD n F) = specialSubgroup (formD n F) ⊓
      (spinorNorm (formD n F) polarD_nondegenerate h2).ker := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2,by omega⟩
  exact elementaryD_eq_intrinsicKernel k h2

/-- In even characteristic the actual full-group residual-parity character has
kernel Omega; the character and its value formula are both explicitly retained. -/
theorem DPlus_even_intrinsic (n : ℕ) (hn : 4 ≤ n) (h2 : (2 : F) = 0) :
    ∃ χ : O_DPlus n F →* Multiplicative (ZMod 2),
      (∀ g, (χ g).toAdd = dicksonValue (formD n F) g) ∧
      Function.Surjective χ ∧ χ.ker = elementarySubgroup (formD n F) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3,by omega⟩
  letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  exact ⟨fullDicksonD k,fullDicksonD_value k,fullDicksonD_surjective k,fullDicksonD_kernel_elementary k⟩

end Atlas.Orthogonal

namespace Atlas
open Orthogonal

/-- The verified public package concerns the actual quadratic-form group DPlus n F.
The public rank bound is four; there are no excluded fields in this range. -/
structure TypeDConstruction (n : ℕ) (F : Type*) [Field F] : Prop where
  rank_bound : 4 ≤ n
  finite_full : Finite (O_DPlus n F)
  full_order : Nat.card (O_DPlus n F) = 2 * DPlus_order_numerator n (Nat.card F)
  elementary_order_exact : Nat.card (elementarySubgroup (formD n F)) * Nat.gcd 2 (Nat.card F - 1) =
    DPlus_order_numerator n (Nat.card F)
  elementary_order : Nat.card (elementarySubgroup (formD n F)) =
    DPlus_order_numerator n (Nat.card F) / Nat.gcd 2 (Nat.card F - 1)
  elementary_index : (elementarySubgroup (formD n F)).index = 2 * Nat.gcd 2 (Nat.card F - 1)
  center_order_exact : Nat.card (Subgroup.center (elementarySubgroup (formD n F))) *
    Nat.gcd 2 (Nat.card F - 1) = DPlus_order_denominator n (Nat.card F)
  scalar_order_exact : Nat.card (elementaryScalarSubgroup (formD n F)) *
    Nat.gcd 2 (Nat.card F - 1) = DPlus_order_denominator n (Nat.card F)
  center_order : Nat.card (Subgroup.center (elementarySubgroup (formD n F))) =
    DPlus_order_denominator n (Nat.card F) / Nat.gcd 2 (Nat.card F - 1)
  odd_intrinsic : ∀ h2 : (2 : F) ≠ 0, elementarySubgroup (formD n F) =
    specialSubgroup (formD n F) ⊓ (spinorNorm (formD n F) polarD_nondegenerate h2).ker
  even_intrinsic : (2 : F) = 0 → ∃ χ : O_DPlus n F →* Multiplicative (ZMod 2),
    (∀ g, (χ g).toAdd = dicksonValue (formD n F) g) ∧
    Function.Surjective χ ∧ χ.ker = elementarySubgroup (formD n F)
  finite_elementary : Finite (elementarySubgroup (formD n F))
  finite : Finite (DPlus n F)
  denominator_positive : 0 < DPlus_order_denominator n (Nat.card F)
  numerator_positive : 0 < DPlus_order_numerator n (Nat.card F)
  order_exact : Nat.card (DPlus n F) * DPlus_order_denominator n (Nat.card F) =
    DPlus_order_numerator n (Nat.card F)
  order_divisibility : DPlus_order_denominator n (Nat.card F) ∣ DPlus_order_numerator n (Nat.card F)
  order : Nat.card (DPlus n F) = DPlus_order n (Nat.card F)
  simple : IsSimpleGroup (DPlus n F)
  nonabelian : ¬ IsMulCommutative (DPlus n F)
  perfect_elementary : Group.IsPerfect (elementarySubgroup (formD n F))
  perfect : Group.IsPerfect (DPlus n F)
  elementary_equals_derived : elementarySubgroup (formD n F) = commutator (O_DPlus n F)
  scalar_equals_center : elementaryScalarSubgroup (formD n F) =
    Subgroup.center (elementarySubgroup (formD n F))
  scalar_normal : (elementaryScalarSubgroup (formD n F)).Normal
  quotient_surjective : Function.Surjective (projectiveElementaryMap (formD n F))
  quotient_kernel : (projectiveElementaryMap (formD n F)).ker = elementaryScalarSubgroup (formD n F)
  faithful : FaithfulSMul (DPlus n F) (SingularPoints (formD n F))
  transitive : MulAction.IsPretransitive (DPlus n F) (SingularPoints (formD n F))
  primitive : MulAction.IsPreprimitive (DPlus n F) (SingularPoints (formD n F))
  root_groups_abelian : ∀ p : SingularPoints (formD n F),
    IsMulCommutative (projectiveRootSubgroup (formD n F) p)
  root_groups_normal_generate : ∀ p : SingularPoints (formD n F),
    Subgroup.normalClosure (projectiveRootSubgroup (formD n F) p : Set (DPlus n F)) = ⊤

theorem typeD_construction {F : Type*} [Field F] [Finite F] (n : ℕ) (hn : 4 ≤ n) :
    TypeDConstruction n F := by
  have hq : 2 ≤ Nat.card F := by have h := Finite.one_lt_card (α := F); omega
  exact {
    rank_bound := hn
    finite_full := inferInstance
    full_order := DPlus_full_order n hn
    elementary_order_exact := DPlus_elementary_order_exact n hn
    elementary_order := DPlus_elementary_order n hn
    elementary_index := DPlus_elementary_index n hn
    center_order_exact := DPlus_center_order_exact n hn
    scalar_order_exact := DPlus_scalar_order_exact n hn
    center_order := DPlus_center_order n hn
    odd_intrinsic := DPlus_odd_intrinsic n hn
    even_intrinsic := DPlus_even_intrinsic n hn
    finite_elementary := inferInstance
    finite := DPlus_finite n hn
    denominator_positive := DPlus_order_denominator_positive n (Nat.card F)
    numerator_positive := DPlus_order_numerator_positive n (Nat.card F) hn hq
    order_exact := DPlus_card_mul_denominator n hn
    order_divisibility := DPlus_order_divisibility n hn
    order := DPlus_card n hn
    simple := DPlus_simple n hn
    nonabelian := DPlus_noncommutative n hn
    perfect_elementary := DPlus_elementary_perfect n hn
    perfect := DPlus_perfect n hn
    elementary_equals_derived := DPlus_elementary_eq_derived n hn
    scalar_equals_center := DPlus_scalar_eq_center n hn
    scalar_normal := inferInstance
    quotient_surjective := projectiveElementaryMap_surjective _
    quotient_kernel := projectiveElementaryMap_kernel _
    faithful := DPlus_faithful n hn
    transitive := DPlus_transitive n hn
    primitive := DPlus_primitive n hn
    root_groups_abelian := fun _ => inferInstance
    root_groups_normal_generate := DPlus_roots_normal_generate n hn }

/-- The existence witness is the actual scalar quotient with its singular-line action. -/
theorem exists_typeD {F : Type u} [Field F] [Finite F] (n : ℕ) (hn : 4 ≤ n) :
    ∃ (G : Type u) (_ : Group G) (_ : MulAction G (SingularPoints (formD n F))),
      Finite G ∧ IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧
      Nat.card G = DPlus_order n (Nat.card F) ∧ FaithfulSMul G (SingularPoints (formD n F)) ∧
      Nonempty (G ≃* DPlus n F) ∧ TypeDConstruction n F := by
  have hc := typeD_construction (F := F) n hn
  exact ⟨DPlus n F,inferInstance,inferInstance,hc.finite,hc.simple,hc.nonabelian,
    hc.order,hc.faithful,⟨MulEquiv.refl _⟩,hc⟩

/-- Every prime, positive exponent and public split-D rank is realized by mathlib's
actual Galois field and the retained quadratic-form construction. -/
theorem typeD_prime_power (p f n : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hn : 4 ≤ n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ TypeDConstruction n F := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := GaloisField.card p f (by omega)
  exact ⟨GaloisField p f,inferInstance,inferInstance,hc,typeD_construction n hn⟩
end Atlas
