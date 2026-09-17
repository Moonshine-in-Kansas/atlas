import Atlas.Fischer.OctadicRootFibres
import Atlas.Algebra.BinaryWalsh

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- The existing integer binary character, embedded into the actual scalar field. -/
theorem parkerScalarSign_walsh (b : Bit) :
    parkerScalarSign b = (Atlas.Algebra.binaryWalshSign b : Scalar) := by
  simp only [parkerScalarSign, Atlas.Algebra.binaryWalshSign]
  split_ifs <;> norm_num

theorem parkerScalarSign_sum {V : Type*} [AddCommGroup V] [Fintype V]
    (a : V →+ Bit) :
    (∑ x, parkerScalarSign (a x)) = if a = 0 then (Fintype.card V : Scalar) else 0 := by
  simp only [parkerScalarSign_walsh, ← Int.cast_sum]
  rw [Atlas.Algebra.binaryWalshChar_sum]
  split_ifs <;> norm_num

/-- Orthogonality on the actual shortened code, before deleting 0 and X. -/
theorem octadEvaluation_sign_pair_sum (O : Octad) (i j : OctadExterior O) :
    (∑ b : octadShortenedCode O,
      parkerScalarSign (octadEvaluation O i b) * parkerScalarSign (octadEvaluation O j b)) =
      if i = j then (32 : Scalar) else 0 := by
  have hz : (octadEvaluation O i + octadEvaluation O j).toAddMonoidHom = 0 ↔ i = j := by
    constructor
    · intro h
      apply octadEvaluation_injective O
      ext b
      have hh := congrArg (fun a : octadShortenedCode O →+ Bit => a b) h
      change octadEvaluation O i b + octadEvaluation O j b = 0 at hh
      have hb : ∀ x y : Bit, x + y = 0 → x = y := by decide
      exact hb _ _ hh
    · rintro rfl
      ext b
      change octadEvaluation O i b + octadEvaluation O i b = 0
      exact CharTwo.add_self_eq_zero _
  have hc : Fintype.card (octadShortenedCode O) = 32 := by
    rw [← Nat.card_eq_fintype_card, octadShortenedCode_card]
  simp_rw [← parkerScalarSign_add]
  change (∑ b, parkerScalarSign ((octadEvaluation O i + octadEvaluation O j).toAddMonoidHom b)) = _
  rw [parkerScalarSign_sum, hc]
  simp only [hz]; norm_num


/-- Deleting the zero and all-one words leaves the exact thirty versus negative-two Gram matrix. -/
theorem octadEvaluation_hyperplane_sign_pair_sum (O : Octad) (i j : OctadExterior O) :
    (∑ b : OctadShortenedHyperplane O,
      parkerScalarSign (octadEvaluation O i b.val) * parkerScalarSign (octadEvaluation O j b.val)) =
      if i = j then (30 : Scalar) else -2 := by
  classical
  let F (b : octadShortenedCode O) :=
    parkerScalarSign (octadEvaluation O i b) * parkerScalarSign (octadEvaluation O j b)
  have he : (∑ b : OctadShortenedHyperplane O, F b.val) =
      ∑ b ∈ ({0, octadShortenedOne O}ᶜ : Finset (octadShortenedCode O)), F b := by
    symm
    apply Finset.sum_subtype
    intro b
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
  change (∑ b : OctadShortenedHyperplane O, F b.val) = _
  rw [he]
  have ht := Finset.sum_compl_add_sum (s := {0, octadShortenedOne O}) F
  have hn : (0 : octadShortenedCode O) ∉ ({octadShortenedOne O} : Finset _) := by
    simpa only [Finset.mem_singleton] using Ne.symm (octadShortenedOne_ne_zero O)
  rw [Finset.sum_insert hn, Finset.sum_singleton] at ht
  have hz : F 0 = 1 := by simp [F, parkerScalarSign]
  have hX : F (octadShortenedOne O) = 1 := by simp [F, parkerScalarSign]
  rw [hz, hX] at ht
  have hf : (∑ b, F b) = if i = j then (32 : Scalar) else 0 :=
    octadEvaluation_sign_pair_sum O i j
  rw [hf] at ht
  split_ifs at ht ⊢ with h <;> linear_combination ht

end Atlas.Fischer

