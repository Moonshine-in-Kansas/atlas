import Atlas.Fischer.DuadMixedTermSigns
import Atlas.Fischer.DuadCoordinateFormulaTransport

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem golayCoordinateVector_congr {a b : golay}
    (ha : hammingNorm a.val=8 ∨ hammingNorm a.val=16)
    (hb : hammingNorm b.val=8 ∨ hammingNorm b.val=16) (h : a=b) :
    golayCoordinateVector a ha=golayCoordinateVector b hb := by
  subst b
  rfl

/-- Every word pair contributing a coordinate has exactly the required signed
half coefficient, including both pure and mixed pairs. -/
theorem duadWordPair_global_sign {F G : Octad}
    (hFG : (F.val ∩ G.val).card = 2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (b : octadShortenedCode F) (c : octadShortenedCode G)
    (hw : hammingNorm (b.val+c.val).val=8 ∨ hammingNorm (b.val+c.val).val=16) :
    ∃ e : Bit, product (octadicWordTerm Q b) (octadicWordTerm R c) =
      (parkerScalarSign e / 2) • golayCoordinateVector (b.val+c.val) hw := by
  by_cases hb : b=0
  · subst b
    have hc : c ≠ 0 := by
      intro hc
      simp [hc,hammingNorm] at hw
    have hwc : hammingNorm c.val.val=8 ∨ hammingNorm c.val.val=16 := by simpa using hw
    rw [golayCoordinateVector_congr hw hwc (by simp)]
    exact duadPureTerm_global_sign hFG Q R c hc hwc
  by_cases hc : c=0
  · subst c
    have he := duadPureTerm_global_sign
      (show (G.val ∩ F.val).card=2 by simpa only [Finset.inter_comm] using hFG)
      R Q b hb (by simpa using hw)
    have hwb : hammingNorm b.val.val=8 ∨ hammingNorm b.val.val=16 := by simpa using hw
    rw [golayCoordinateVector_congr hw hwb (by simp)]
    simpa only [product_comm] using he
  exact duadMixedTerm_global_sign hFG Q R b c hb hc hw

/-- The sign of each actual nonzero coordinate is derived from its unique
word-pair product and the fixed global zero-sign Parker section. -/
theorem duadZeroWordTerm_global_sign (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) (c : DuadCoordinateWord p) :
    ∃ e : Bit, duadZeroWordTerm p hp F G hFG Q R c.val =
      (parkerScalarSign e / 2) • duadWordVector p c := by
  have hv := congrArg Subtype.val ((duadOctadSumEquiv p hp F G hFG).apply_symm_apply c.val)
  rw [duadOctadSumEquiv_apply] at hv
  have he := duadWordPair_global_sign (hFG ▸ hp) Q R
    ((duadOctadSumEquiv p hp F G hFG).symm c.val).1
    ((duadOctadSumEquiv p hp F G hFG).symm c.val).2 (by simpa only [hv] using c.property)
  obtain ⟨e,he⟩ := he
  refine ⟨e,?_⟩
  change product _ _ = (parkerScalarSign e / 2) • golayCoordinateVector c.val.val c.property
  rw [he,golayCoordinateVector_congr _ c.property hv]

/-- This is a derived binary sign function, not stipulated coefficient data. -/
def duadEta (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) (c : DuadCoordinateWord p) : Bit :=
  (duadZeroWordTerm_global_sign p hp F G hFG Q R c).choose

theorem duadEta_term (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) (c : DuadCoordinateWord p) :
    duadZeroWordTerm p hp F G hFG Q R c.val =
      (parkerScalarSign (duadEta p hp F G hFG Q R c) / 2) • duadWordVector p c :=
  (duadZeroWordTerm_global_sign p hp F G hFG Q R c).choose_spec

/-- The complete zero-character formula has all 407 coefficients, each with
exact magnitude one eighth. -/
theorem duadCharacterProduct_zero_formula (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    duadCharacterProduct p hp F G hFG Q R 0 =
      duadSignedCoordinateExpression p (duadEta p hp F G hFG Q R) 0 := by
  rw [duadCharacterProduct_zero_word_expansion,duadZeroWordTerm_sum]
  simp only [duadEta_term,duadSignedCoordinateExpression,LinearMap.zero_apply,add_zero]
  have hs : (∑ c : DuadCoordinateWord p,
      (parkerScalarSign (duadEta p hp F G hFG Q R c) / 2) • duadWordVector p c) =
      (1/2 : Scalar) • ∑ c : DuadCoordinateWord p,
        parkerScalarSign (duadEta p hp F G hFG Q R c) • duadWordVector p c := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [smul_smul]
    congr 1
    ring
  rw [hs]
  module

/-- Source R1's full character formula for the actual octadic products, with
all signs derived and no coordinate or generation premise. -/
theorem duadCharacterProduct_coordinate_formula (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G)
    (ξ : Module.Dual Bit (duadShortenedCode p)) :
    duadCharacterProduct p hp F G hFG Q R ξ =
      duadSignedCoordinateExpression p (duadEta p hp F G hFG Q R) ξ :=
  duadCharacterProduct_formula_of_zero p hp F G hFG Q R _
    (duadCharacterProduct_zero_formula p hp F G hFG Q R) ξ

end Atlas.Fischer
