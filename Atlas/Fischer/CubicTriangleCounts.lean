import Atlas.Fischer.CubicTriangleModels

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def cubicSextetTrianglePairEquiv : OrderedCubicSextetTriangle ≃
    Σ D : Octad, CubicOctadIntersectionRow D 4 where
  toFun t := ⟨t.val.1,t.val.2.1,by
    simpa only [signedOctadIntersection,signedOctadSupport_canonical] using
      octadWord_sum_weight t.val.2.2 t.val.1 t.val.2.1 t.property⟩
  invFun p := ⟨(p.1,p.2.val,cubicSextetCompletion p.1 p.2.val p.2.property),
    cubicSextetCompletion_word p.1 p.2.val p.2.property⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    apply octadWord_injective
    dsimp only
    rw [cubicSextetCompletion_word]
    exact t.property.symm
  right_inv p := by cases p; rfl

def cubicTrioPairEquiv : OrderedCubicTrio ≃
    Σ D : Octad, CubicOctadIntersectionRow D 0 where
  toFun t := ⟨t.val.1,t.val.2.1,by
    simpa only [signedOctadIntersection,signedOctadSupport_canonical] using
      octadWord_complementary_sum_weight t.val.2.2 t.val.1 t.val.2.1 t.property⟩
  invFun p := ⟨(p.1,p.2.val,cubicTrioCompletion p.1 p.2.val p.2.property),
    cubicTrioCompletion_word p.1 p.2.val p.2.property⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    apply octadWord_injective
    dsimp only
    rw [cubicTrioCompletion_word]
    exact t.property.symm
  right_inv p := by cases p; rfl

/-- The triangles are actual ordered triples of Golay octads. -/
theorem orderedCubicSextetTriangle_card : Nat.card OrderedCubicSextetTriangle=759*280 := by
  rw [Nat.card_congr cubicSextetTrianglePairEquiv,Nat.card_sigma]
  simp_rw [cubicOctadIntersectionRow_card]
  have h (D : Octad) : octadIntersectionCount D.val ∅ 4=280 :=
    (octad_intersection_distribution D.val D.property).2.2.1
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [Fintype.card_coe,octads_card]

/-- The trios are actual ordered triples of complementary Golay octads. -/
theorem orderedCubicTrio_card : Nat.card OrderedCubicTrio=759*30 := by
  rw [Nat.card_congr cubicTrioPairEquiv,Nat.card_sigma]
  simp_rw [cubicOctadIntersectionRow_card]
  have h (D : Octad) : octadIntersectionCount D.val ∅ 0=30 :=
    (octad_intersection_distribution D.val D.property).1
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [Fintype.card_coe,octads_card]

end Atlas.Fischer
