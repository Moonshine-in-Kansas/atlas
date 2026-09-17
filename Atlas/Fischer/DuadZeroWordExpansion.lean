import Atlas.Fischer.OctadicWordTermValues
import Atlas.Fischer.DuadMissingWordTerms
import Atlas.Fischer.DuadCharacterProducts
import Atlas.Fischer.DuadAxisProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable
instance duadCoordinateWordFintype (p : Finset Omega) : Fintype (DuadCoordinateWord p) := by
  unfold DuadCoordinateWord
  infer_instance


/-- The actual term belonging to a shortened-duad word under the direct sum. -/
def duadZeroWordTerm (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) (c : duadShortenedCode p) : Coordinates :=
  product (octadicWordTerm Q ((duadOctadSumEquiv p hp F G hFG).symm c).1)
    (octadicWordTerm R ((duadOctadSumEquiv p hp F G hFG).symm c).2)

theorem duadZeroWordTerm_zero (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    duadZeroWordTerm p hp F G hFG Q R 0 = (1/2 : Scalar) • duadicAxisPart p := by
  simp only [duadZeroWordTerm,map_zero,Prod.fst_zero,Prod.snd_zero]
  rw [octadicWordTerm_zero,octadicWordTerm_zero,product_octadicAxis_duad_pair F G (hFG ▸ hp),hFG]

theorem duadCharacterProduct_zero_word_expansion (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    duadCharacterProduct p hp F G hFG Q R 0 =
      (1/4 : Scalar) • ∑ c : duadShortenedCode p, duadZeroWordTerm p hp F G hFG Q R c := by
  simp only [duadCharacterProduct,map_zero,Prod.fst_zero,Prod.snd_zero,duadOctadicProduct]
  rw [product_octadicRoot_word_expansion]
  simp only [LinearMap.zero_apply,show parkerScalarSign 0=1 from rfl,mul_one,one_smul]
  congr 1
  rw [← Equiv.sum_comp (duadOctadSumEquiv p hp F G hFG).toEquiv]
  simp only [duadZeroWordTerm,LinearEquiv.coe_toEquiv,LinearEquiv.symm_apply_apply,Fintype.sum_prod_type]

/-- Only zero and the 407 actual coordinate words remain in the term sum. -/
theorem duadZeroWordTerm_sum (p : Finset Omega) (hp : p.card = 2)
    (F G : Octad) (hFG : F.val ∩ G.val = p)
    (Q : OctadCalibration F) (R : OctadCalibration G) :
    (∑ c : duadShortenedCode p, duadZeroWordTerm p hp F G hFG Q R c) =
      (1/2 : Scalar) • duadicAxisPart p +
        ∑ c : DuadCoordinateWord p, duadZeroWordTerm p hp F G hFG Q R c.val := by
  let P : duadShortenedCode p → Prop := fun c => hammingNorm c.val.val=8 ∨ hammingNorm c.val.val=16
  have h0 : ¬P 0 := by simp [P,hammingNorm]
  rw [← Fintype.sum_subtype_add_sum_subtype P]
  have hz : (∑ c : {c : duadShortenedCode p // ¬P c}, duadZeroWordTerm p hp F G hFG Q R c.val) =
      duadZeroWordTerm p hp F G hFG Q R 0 := by
    refine Finset.sum_eq_single (f := fun c : {c : duadShortenedCode p // ¬P c} =>
      duadZeroWordTerm p hp F G hFG Q R c.val) ⟨0,h0⟩ ?_ ?_
    · intro c _ hc
      apply duadWordPair_missing_zero p hp F G hFG Q R c.val
      · intro he
        apply hc
        exact Subtype.ext he
      · exact c.property
    · simp
  rw [hz,duadZeroWordTerm_zero]
  exact add_comm _ _

end Atlas.Fischer
