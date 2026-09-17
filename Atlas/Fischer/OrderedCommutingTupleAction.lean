import Atlas.Fischer.OrderedCommutingTuples
import Mathlib.GroupTheory.GroupAction.Quotient

noncomputable section
namespace Atlas.Fischer

 def orderedCommutingConjugate {s : ℕ} (g : rootGeneratedRayGroup)
    (t : OrderedCommutingTuple s) : OrderedCommutingTuple s := by
  refine ⟨⟨fun k => MulAut.conj g (t.val k),
    (MulAut.conj g).injective.comp t.val.injective⟩, ?_, ?_⟩
  · intro k
    let i : ReflectingRootParameter := .inl (Classical.choice inferInstance)
    apply (distinguishedRootClass_isConj_iff i _).mpr
    exact ((distinguishedRootClass_isConj_iff i _).mp (t.property.1 k)).trans
      (isConj_iff.mpr ⟨g, rfl⟩)
  · intro k l
    exact (t.property.2 k l).map (MulAut.conj g).toMonoidHom

instance orderedCommutingTupleMulAction (s : ℕ) :
    MulAction rootGeneratedRayGroup (OrderedCommutingTuple s) where
  smul := orderedCommutingConjugate
  one_smul t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro k
    change 1 * t.val k * (1 : rootGeneratedRayGroup)⁻¹ = t.val k
    simp
  mul_smul g h t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro k
    change (g * h) * t.val k * (g * h)⁻¹ =
      g * (h * t.val k * h⁻¹) * g⁻¹
    simp [mul_assoc]

 theorem orderedCommutingTuple_smul_apply {s : ℕ} (g : rootGeneratedRayGroup)
    (t : OrderedCommutingTuple s) (k : Fin s) :
    (g • t).val k = g * t.val k * g⁻¹ := rfl

 theorem orderedCommutingTuple_transitive (s : ℕ) (hs : s ≤ 5) :
    MulAction.IsPretransitive rootGeneratedRayGroup (OrderedCommutingTuple s) := by
  apply MulAction.IsPretransitive.mk
  intro t u
  obtain ⟨g, hg⟩ := commutingTuples_homogeneous hs t.val u.val
    t.property.1 u.property.1 t.property.2 u.property.2
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Function.Embedding.ext
  exact hg

 theorem orderedCommutingTuple_order_product (s : ℕ) (hs : s ≤ 5)
    (t : OrderedCommutingTuple s) :
    Nat.card (OrderedCommutingTuple s) *
      Nat.card (MulAction.stabilizer rootGeneratedRayGroup t) = Nat.card rootGeneratedRayGroup := by
  haveI := orderedCommutingTuple_transitive s hs
  have he : MulAction.orbit rootGeneratedRayGroup t ≃ OrderedCommutingTuple s :=
    Equiv.setCongr (MulAction.orbit_eq_univ rootGeneratedRayGroup t) |>.trans (Equiv.Set.univ _)
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup rootGeneratedRayGroup t)
  rw [Nat.card_prod, Nat.card_congr he] at hc
  exact hc

end Atlas.Fischer
