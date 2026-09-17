import Atlas.Fischer.OctadRationalGrading
import Atlas.Fischer.OctadLabelSeparation
import Atlas.Fischer.OctadicCocodeAction

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Conway
attribute [local instance] Classical.propDecidable

/-- The actual Golay word carried by a rational coordinate; multiplication by
θ adds the all-one word because the cocode action conjugates that scalar. -/
def rationalCoordinateGolayWord (p : RationalCoordinateIndex) : golay :=
  (match p.1 with
    | Sum.inl _ => 0
    | Sum.inr D => octadWord D) + if p.2=0 then 0 else golayOne

def octadRationalCodeLabel (O : Octad) (p : RationalCoordinateIndex) : octadEvenCode O :=
  octadEvenRestriction O (rationalCoordinateGolayWord p)

theorem octadRationalCodeLabel_apply (O : Octad) (p : RationalCoordinateIndex)
    (i : O.val) :
    (octadRationalCodeLabel O p).val i =
      if i.val ∈ octadRationalLabel O p then 1 else 0 := by
  obtain ⟨a,k⟩ := p
  fin_cases k <;> cases a with
  | inl a =>
    simp [octadRationalCodeLabel,octadEvenRestriction,rationalCoordinateGolayWord,
      octadRationalLabel,golayRestriction,golayOne,allOnes,i.prop]
  | inr D =>
    by_cases hi : i.val ∈ D.val <;>
      simp [octadRationalCodeLabel,octadEvenRestriction,rationalCoordinateGolayWord,
        octadRationalLabel,golayRestriction,octadWord_apply,golayOne,allOnes,hi,i.prop]

theorem octadRationalLabel_subset (O : Octad) (p : RationalCoordinateIndex) :
    octadRationalLabel O p ⊆ O.val := by
  obtain ⟨a,k⟩ := p
  fin_cases k <;> cases a <;>
    simp [octadRationalLabel,Finset.inter_subset_right,Finset.sdiff_subset]

theorem octadRationalCodeLabel_eq_iff (O : Octad) (p q : RationalCoordinateIndex) :
    octadRationalCodeLabel O p=octadRationalCodeLabel O q ↔
      octadRationalLabel O p=octadRationalLabel O q := by
  constructor
  · intro h
    apply Finset.ext
    intro i
    by_cases hi : i ∈ O.val
    · have he := congrArg (fun a : octadEvenCode O => a.val ⟨i,hi⟩) h
      rw [octadRationalCodeLabel_apply,octadRationalCodeLabel_apply] at he
      by_cases hp : i ∈ octadRationalLabel O p <;>
        by_cases hq : i ∈ octadRationalLabel O q <;> simp_all
    · have hp : i ∉ octadRationalLabel O p := fun h => hi (octadRationalLabel_subset O p h)
      have hq : i ∉ octadRationalLabel O q := fun h => hi (octadRationalLabel_subset O q h)
      simp [hp,hq]
  · intro h
    apply Subtype.ext
    funext i
    rw [octadRationalCodeLabel_apply,octadRationalCodeLabel_apply,h]

def rationalBitSign (b : Bit) : ℚ := if b=0 then 1 else -1

theorem rationalBitSign_injective : Function.Injective rationalBitSign := by
  intro a b
  have hb : ∀ t : Bit, t=0 ∨ t=1 := by decide
  rcases hb a with rfl | rfl <;> rcases hb b with rfl | rfl <;>
    norm_num [rationalBitSign]

theorem rationalBitSign_cast (b : Bit) : (rationalBitSign b : Scalar)=parkerScalarSign b := by
  by_cases hb : b=0 <;> simp [rationalBitSign,parkerScalarSign,hb]

end Atlas.Fischer
