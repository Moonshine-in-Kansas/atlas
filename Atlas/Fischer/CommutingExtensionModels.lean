import Atlas.Fischer.CommutingTupleHomogeneity
import Atlas.Fischer.MarkedBasicExtensionRays

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

abbrev CommutingExtension {s : ℕ} (t : Fin s ↪ rootGeneratedRayGroup) :=
  {x : rootGeneratedRayGroup // x ∈ Set.range distinguishedRootElement ∧
    ∀ k, x ≠ t k ∧ Commute (t k) x}

theorem distinguishedRoot_commute_iff (i j : ReflectingRootParameter) :
    Commute (distinguishedRootElement i) (distinguishedRootElement j) ↔
      hermitian (reflectingRootParameterVector i) (reflectingRootParameterVector j) ≠ 0 := by
  refine ⟨distinguishedRoot_commute_nonzero i j,?_⟩
  intro hn
  by_cases hij : i=j
  · subst j; exact Commute.refl _
  have hp := distinguishedRootElement_product_order i j hij
  rw [if_neg hn] at hp
  have hs : (distinguishedRootElement i * distinguishedRootElement j)^2=1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hp])
  have hi : (distinguishedRootElement i)⁻¹=distinguishedRootElement i :=
    inv_eq_of_mul_eq_one_right (by
      have h := orderOf_dvd_iff_pow_eq_one.mp (show orderOf (distinguishedRootElement i) ∣ 2 by
        rw [distinguishedRootElement_order])
      simpa only [pow_two] using h)
  have hj : (distinguishedRootElement j)⁻¹=distinguishedRootElement j :=
    inv_eq_of_mul_eq_one_right (by
      have h := orderOf_dvd_iff_pow_eq_one.mp (show orderOf (distinguishedRootElement j) ∣ 2 by
        rw [distinguishedRootElement_order])
      simpa only [pow_two] using h)
  have ht := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  change distinguishedRootElement i * distinguishedRootElement j = _
  rw [← ht,mul_inv_rev,hi,hj]

def basicCommutingTuple {s : ℕ} (a : Fin s ↪ Omega) : Fin s ↪ rootGeneratedRayGroup :=
  ⟨fun k => distinguishedRootElement (.inl (a k)), fun k l h =>
    a.injective (Sum.inl.inj (distinguishedRootElement_injective h))⟩

/-- The marked support-count predicate is exactly the group-theoretic extension predicate. -/
theorem markedBasicExtension_group_iff {s : ℕ} (a : Fin s ↪ Omega)
    (t : ReflectingRootParameter) :
    IsMarkedBasicExtension (Finset.univ.image a) t ↔
      ∀ k, distinguishedRootElement t ≠ basicCommutingTuple a k ∧
        Commute (basicCommutingTuple a k) (distinguishedRootElement t) := by
  classical
  unfold IsMarkedBasicExtension
  simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, basicCommutingTuple, Function.Embedding.coeFn_mk,
    distinguishedRoot_commute_iff]
  apply forall_congr'
  intro k
  change (reflectingRootParameterRay t ≠ reflectingRootParameterRay (.inl (a k)) ∧ _) ↔
    (distinguishedRootElement t ≠ distinguishedRootElement (.inl (a k)) ∧
      Commute (distinguishedRootElement (.inl (a k))) (distinguishedRootElement t))
  rw [distinguishedRoot_commute_iff]
  apply and_congr_left
  intro _
  exact not_congr (reflectingRootParameterRay_injective.eq_iff.trans
    distinguishedRootElement_injective.eq_iff.symm)

def markedBasicExtensionGroupEquiv {s : ℕ} (a : Fin s ↪ Omega) :
    MarkedBasicExtension (Finset.univ.image a) ≃ CommutingExtension (basicCommutingTuple a) :=
  Equiv.ofBijective (fun t => ⟨distinguishedRootElement t.val, ⟨t.val,rfl⟩,
    (markedBasicExtension_group_iff a t.val).mp t.property⟩)
    ⟨fun x y h => Subtype.ext (distinguishedRootElement_injective (congrArg Subtype.val h)), by
      rintro ⟨x,⟨t,rfl⟩,ht⟩
      exact ⟨⟨t,(markedBasicExtension_group_iff a t).mpr ht⟩,rfl⟩⟩

end Atlas.Fischer
