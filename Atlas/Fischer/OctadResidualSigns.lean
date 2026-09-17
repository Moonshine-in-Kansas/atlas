import Atlas.Fischer.OctadSeparatingGraph
import Atlas.Fischer.CubicTriangleModels
import Atlas.Fischer.OctadShortenedCode

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

private theorem sextetCompletion_mem (D E : Octad)
    (h : (D.val ∩ E.val).card = 4) (i : Omega) :
    i ∈ (cubicSextetCompletion D E h).val ↔
      (i ∈ D.val ∧ i ∉ E.val) ∨ (i ∈ E.val ∧ i ∉ D.val) := by
  have he := congrArg (fun c : golay => c.val i) (cubicSextetCompletion_word D E h)
  change (octadWord (cubicSextetCompletion D E h)).val i =
    (octadWord D).val i + (octadWord E).val i at he
  rw [octadWord_apply, octadWord_apply, octadWord_apply] at he
  by_cases hD : i ∈ D.val <;> by_cases hE : i ∈ E.val <;>
    by_cases hF : i ∈ (cubicSextetCompletion D E h).val <;> simp_all

private theorem connected_constant {V : Type*} (G : SimpleGraph V)
    (hc : G.Connected) (f : V → Bit)
    (he : ∀ x y, G.Adj x y → f x = f y) (x y : V) : f x = f y := by
  obtain ⟨w⟩ := hc x y
  induction w with
  | nil => rfl
  | cons h w ih => exact (he _ _ h).trans ih

/-- The residual signs on actual octads extend to a character supported on the
specified two coordinates. Only the explicit intersection-four relations are used. -/
theorem octad_residual_sign_extension (i j : Omega) (hij : i ≠ j)
    (μ : Octad → Bit) (ε : Bit)
    (hadd : ∀ D E (h : (D.val ∩ E.val).card = 4),
      μ (cubicSextetCompletion D E h) = μ D + μ E)
    (hzero : ∀ D, i ∉ D.val → j ∉ D.val → μ D = 0)
    (hboth : ∀ D, i ∈ D.val → j ∈ D.val → μ D = ε) :
    ∃ a b : Bit, a + b = ε ∧ ∀ D : Octad,
      μ D = a * (if i ∈ D.val then 1 else 0) +
        b * (if j ∈ D.val then 1 else 0) := by
  have hconst (u v : Omega) (huv : u ≠ v)
      (hz : ∀ D : Octad, u ∉ D.val → v ∉ D.val → μ D = 0)
      (A B : OctadSeparatingVertex u v) : μ A.val = μ B.val := by
    apply connected_constant (octadSeparatingGraph u v)
      (octadSeparatingGraph_connected u v huv) (fun D => μ D.val) _ A B
    intro D E hDE
    have h4 : (D.val.val ∩ E.val.val).card = 4 := by
      simpa only [octadSeparatingGraph, Finset.inter_comm] using hDE
    have hz' : μ (cubicSextetCompletion D.val E.val h4) = 0 := by
      apply hz
      · rw [sextetCompletion_mem]; simp [D.property.1, E.property.1]
      · rw [sextetCompletion_mem]; simp [D.property.2, E.property.2]
    have hs := hadd D.val E.val h4
    have hh : μ D.val + μ E.val = 0 := hs.symm.trans hz'
    have : μ D.val = - μ E.val := eq_neg_of_add_eq_zero_left hh
    simpa using this
  have hn : Nonempty (OctadSeparatingVertex i j) := by
    apply (Nat.card_pos_iff.mp ?_).1
    rw [octadSeparatingVertex_card i j hij]
    norm_num
  let D := Classical.choice hn
  have hn' : Nonempty {E : OctadSeparatingVertex j i //
      (E.val.val ∩ D.val.val).card = 4} := by
    apply (Nat.card_pos_iff.mp ?_).1
    rw [octadSeparating_cross_vertex_card i j D]
    norm_num
  let E := (Classical.choice hn').val
  have h4 : (D.val.val ∩ E.val.val).card = 4 := by
    rw [Finset.inter_comm]
    exact (Classical.choice hn').property
  have hs : μ D.val + μ E.val = ε := by
    rw [← hadd D.val E.val h4]
    apply hboth
    · rw [sextetCompletion_mem]; exact Or.inl ⟨D.property.1, E.property.2⟩
    · rw [sextetCompletion_mem]; exact Or.inr ⟨E.property.1, D.property.2⟩
  refine ⟨μ D.val, μ E.val, hs, ?_⟩
  intro F
  by_cases hi : i ∈ F.val <;> by_cases hj : j ∈ F.val
  · simpa only [hi, hj, ite_true, mul_one] using (hboth F hi hj).trans hs.symm
  · simpa only [hi, hj, ite_true, ite_false, mul_one, mul_zero, add_zero] using
      hconst i j hij hzero ⟨F, hi, hj⟩ D
  · simpa only [hi, hj, ite_true, ite_false, mul_one, mul_zero, zero_add] using
      hconst j i hij.symm (fun F hj hi => hzero F hi hj) ⟨F, hj, hi⟩ E
  · simpa only [hi, hj, ite_false, mul_zero, add_zero] using hzero F hi hj

end Atlas.Fischer
