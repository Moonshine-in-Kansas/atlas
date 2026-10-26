import Atlas.LinearGroups.ReeF4.WeylSL2Product
import Mathlib.Algebra.Group.Units.Equiv

/-! Every element of the full retained torus belongs to the actual SL₂×F×
product subgroup, by the unique-square-root property in characteristic two. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem exists_longSL2_torus_factors (a b : Fˣ) :
    ∃ s c : Fˣ, a = s*c ∧ b = s⁻¹*c := by
  obtain ⟨s,hs⟩ := (Units.mapEquiv (frobeniusEquiv F 2).toMulEquiv).surjective (a*b⁻¹)
  have hsq : s^2 = a*b⁻¹ := by
    apply Units.ext
    have hh := congrArg (fun z : Fˣ => (z : F)) hs
    change (s : F)^2 = ((a*b⁻¹ : Fˣ) : F) at hh
    change (s : F)^2 = ((a*b⁻¹ : Fˣ) : F)
    exact hh
  refine ⟨s,b*s,?_,?_⟩
  · calc
      a = (a*b⁻¹)*b := by simp [mul_assoc]
      _ = s^2*b := by rw [hsq]
      _ = s*(b*s) := by simp only [pow_two, mul_assoc, mul_left_comm, mul_comm]
  · simp [mul_assoc, mul_left_comm, mul_comm]

theorem modelLongSL2Product_diagonal {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (s c : Fˣ) :
    modelLongSL2ProductHom hcard (longSL2DiagonalMatrix s,c) =
      torusModelHom hcard (s*c,s⁻¹*c) := by
  apply Subtype.ext
  change longSL2Representation (theta F m).toRingHom (longSL2DiagonalMatrix s) *
    torusEquiv m c c = torusEquiv m (s*c) (s⁻¹*c)
  rw [longSL2Representation_torus]
  exact ((torusHom (F := F) m).map_mul (s,s⁻¹) (c,c)).symm

theorem torusModelHom_mem_longSL2Product {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : Fˣ) :
    torusModelHom hcard (a,b) ∈ modelLongSL2ProductSubgroup hcard := by
  obtain ⟨s,c,ha,hb⟩ := exists_longSL2_torus_factors a b
  refine ⟨(longSL2DiagonalMatrix s,c),?_⟩
  rw [modelLongSL2Product_diagonal, ← ha, ← hb]

theorem torusModelHom_range_le_longSL2Product {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    (torusModelHom hcard).range ≤ modelLongSL2ProductSubgroup hcard := by
  rintro _ ⟨⟨a,b⟩,rfl⟩
  exact torusModelHom_mem_longSL2Product hcard a b

theorem longSL2Model_range_le_product {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    (modelLongSL2Hom hcard).range ≤ modelLongSL2ProductSubgroup hcard := by
  rintro _ ⟨A,rfl⟩
  refine ⟨(A,1),?_⟩
  change modelLongSL2Hom hcard A * modelLongSL2ScalarHom hcard 1 = _
  rw [map_one,mul_one]

theorem modelLongSL2Product_eq_sup_torus {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) :
    modelLongSL2ProductSubgroup hcard =
      (modelLongSL2Hom hcard).range ⊔ (torusModelHom hcard).range := by
  apply le_antisymm
  · rintro _ ⟨⟨A,c⟩,rfl⟩
    change modelLongSL2Hom hcard A * torusModelHom hcard (c,c) ∈ _
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ⟨A,rfl⟩) (Subgroup.mem_sup_right ⟨(c,c),rfl⟩)
  · exact sup_le (longSL2Model_range_le_product hcard)
      (torusModelHom_range_le_longSL2Product hcard)

end Atlas.ReeF4
