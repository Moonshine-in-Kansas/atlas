import Atlas.LinearGroups.ReeF4.TorusWeights

/-! The source SL₂ parameter is fixed by its first natural summand. -/
namespace Atlas.ReeF4
variable {G : Type*} [CommGroup G]

@[simp] theorem longSL2_weight_first_positive (m : ℕ) (a : G) :
    torusWeight m a a⁻¹ (2,7) = a := by
  simp [torusWeight, torusWeightExponents]

@[simp] theorem longSL2_weight_first_negative (m : ℕ) (a : G) :
    torusWeight m a a⁻¹ (0,7) = a⁻¹ := by
  simp [torusWeight, torusWeightExponents]

@[simp] theorem longSL2_weight_self_tensor_positive (m : ℕ) (a : G) :
    torusWeight m a a⁻¹ (1,3) = a ^ 2 := by
  simp [torusWeight, torusWeightExponents, pow_two]

@[simp] theorem longSL2_weight_self_tensor_negative (m : ℕ) (a : G) :
    torusWeight m a a⁻¹ (1,4) = (a⁻¹) ^ 2 := by
  simp [torusWeight, torusWeightExponents, pow_two]

end Atlas.ReeF4
