import Atlas.Fischer.CubicQuadrilateralCounts

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cubicSum_subtype {A : Type*} [Fintype A] (P : A → Prop)
    [Fintype (Subtype P)] (f : A → Scalar) :
    (∑ a, if P a then f a else 0) = ∑ a : Subtype P,f a.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro a; simp) f

theorem cubicPairIndicator_count {A B : Type*} [Fintype A] [Fintype B]
    (P : A → Prop) (Q : A → B → Prop) :
    (∑ a,∑ b,if P a ∧ Q a b then (1 : Scalar) else 0) =
      (Nat.card (Σ a : Subtype P, Subtype (Q a.val)) : Scalar) := by
  have ht (a : A) : (∑ b,if P a ∧ Q a b then (1 : Scalar) else 0) =
      if P a then ∑ b,if Q a b then (1 : Scalar) else 0 else 0 := by
    by_cases h : P a <;> simp [h]
  simp_rw [ht]
  rw [cubicSum_subtype]
  simp_rw [cubicSum_subtype]
  rw [Nat.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp [Nat.card_eq_fintype_card]

theorem cubicQuadrilateral_indicator (D : Octad) (a b c : ℕ) :
    (∑ F : Octad,∑ G : Octad,if (D.val ∩ F.val).card = a ∧
      (D.val ∩ G.val).card = b ∧ (F.val ∩ G.val).card = c then (1 : Scalar) else 0) =
      (Nat.card (CubicQuadrilateralFibre D a b c) : Scalar) :=
  by
    convert cubicPairIndicator_count (fun F : Octad => (D.val ∩ F.val).card = a)
      (fun F G : Octad => (D.val ∩ G.val).card = b ∧ (F.val ∩ G.val).card = c) using 1
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> rfl

theorem cubicQuadrilateral_refined_indicator (D : Octad) (u : ℕ) :
    (∑ F : Octad,∑ G : Octad,if (D.val ∩ F.val).card = 4 ∧
      (D.val ∩ G.val).card = 4 ∧ (F.val ∩ G.val).card = 4 ∧
      (D.val ∩ F.val ∩ G.val).card = u then (1 : Scalar) else 0) =
      (Nat.card (CubicQuadrilateralRefinedFibre D u) : Scalar) :=
  by
    convert cubicPairIndicator_count (fun F : Octad => (D.val ∩ F.val).card = 4)
      (fun F G : Octad => (D.val ∩ G.val).card = 4 ∧ (F.val ∩ G.val).card = 4 ∧
        (D.val ∩ F.val ∩ G.val).card = u) using 1
    apply Finset.sum_congr rfl
    intro F _
    apply Finset.sum_congr rfl
    intro G _
    split_ifs <;> rfl

end Atlas.Fischer
