import Atlas.Fischer.PointwiseAxisFixedDuadWord
import Atlas.Fischer.DuadEtaConstruction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The retained zero-character eta for the already chosen actual duad model. -/
def chosenDuadEta (p : RootDuad) : DuadCoordinateWord p.val → Bit :=
  duadEta p.val p.property
    (duadChosenOctadPair p.val p.property).1 (duadChosenOctadPair p.val p.property).2
    (duadChosenOctadPair_intersection p.val p.property)
    (chosenOctadCalibration _) (chosenOctadCalibration _)

theorem chosenDuadicRoot_coordinate_formula (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val)) :
    chosenDuadicRoot p ξ=duadSignedCoordinateExpression p.val (chosenDuadEta p) ξ :=
  duadCharacterProduct_coordinate_formula p.val p.property _ _
    (duadChosenOctadPair_intersection p.val p.property) _ _ ξ

/-- A fixed actual duadic root forces sign zero on every octad avoiding its duad. -/
theorem pointwiseAxis_fixed_duad_avoiding (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val))
    (hfix : e.val (chosenDuadicRoot p ξ)=chosenDuadicRoot p ξ)
    (D : Octad) (hD : Disjoint p.val D.val) : pointwiseAxisOctadSign e D=0 := by
  classical
  obtain ⟨c,hc⟩ := (duadWeightEightEquiv p.val).surjective ⟨D,hD⟩
  let w : DuadCoordinateWord p.val := ⟨c.val,Or.inl c.property⟩
  have hw : duadWordOctad p.val w=D := by
    change (if h8 : hammingNorm c.val.val.val=8 then golayOctadOfWeight c.val.val h8 else _)=D
    rw [dif_pos c.property]
    exact congrArg Subtype.val hc
  have hp : p.val.Nonempty := Finset.card_pos.mp (by rw [p.property]; decide)
  simp only [chosenDuadicRoot_coordinate_formula] at hfix
  have h := pointwiseAxis_fixed_duad_word_sign e he p.val hp (chosenDuadEta p) ξ hfix w
  rw [hw,if_pos c.property] at h
  exact h

/-- The complementary weight-sixteen coefficients force the parity sign on
every octad containing the duad. -/
theorem pointwiseAxis_fixed_duad_containing (e : SemilinearAlgebraAutomorphism)
    (he : ∀ i, e.val (u i)=u i) (p : RootDuad)
    (ξ : Module.Dual Bit (duadShortenedCode p.val))
    (hfix : e.val (chosenDuadicRoot p ξ)=chosenDuadicRoot p ξ)
    (D : Octad) (hD : p.val ⊆ D.val) :
    pointwiseAxisOctadSign e D=semilinearAlgebraParity e := by
  classical
  obtain ⟨c,hc⟩ := (duadWeightSixteenEquiv p.val).surjective ⟨D,hD⟩
  let w : DuadCoordinateWord p.val := ⟨c.val,Or.inr c.property⟩
  have h8 : hammingNorm c.val.val.val ≠ 8 := by rw [c.property]; decide
  have hw : duadWordOctad p.val w=D := by
    unfold duadWordOctad
    rw [dif_neg h8]
    exact congrArg Subtype.val hc
  have hp : p.val.Nonempty := Finset.card_pos.mp (by rw [p.property]; decide)
  simp only [chosenDuadicRoot_coordinate_formula] at hfix
  have h := pointwiseAxis_fixed_duad_word_sign e he p.val hp (chosenDuadEta p) ξ hfix w
  rw [hw,if_neg h8] at h
  exact h

end Atlas.Fischer
