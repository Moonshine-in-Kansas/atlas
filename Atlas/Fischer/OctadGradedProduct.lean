import Atlas.Fischer.OctadCommonEigenspaces
import Atlas.Fischer.ParkerMultiplicativity
import Atlas.Fischer.ProductMaps
import Mathlib.Data.Finset.SymmDiff

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped symmDiff
attribute [local instance] Classical.propDecidable

theorem octadCommonEigenvector_product (O : Octad) (a b : octadEvenCode O)
    (x y : Coordinates) (hx : OctadCommonEigenvector O a x)
    (hy : OctadCommonEigenvector O b y) : OctadCommonEigenvector O (a+b) (product x y) := by
  intro d
  rw [parkerCoordinateAction_product,hx d,hy d,map_add]
  have hn₁ : product (-x) y = -product x y := map_neg (productLeftMap y) x
  have hn₂ : product x (-y) = -product x y := map_neg (productRightMap x) y
  have hn₃ : product (-x) (-y) = product x y := by
    rw [show product (-x) (-y) = -product x (-y) from map_neg (productLeftMap (-y)) x,hn₂,neg_neg]
  have hb : ∀ t : Bit, t=0 ∨ t=1 := by decide
  rcases hb (octadLabelCharacter O d a) with ha | ha <;>
    rcases hb (octadLabelCharacter O d b) with hb | hb <;>
    simp [ha,hb,rationalBitSign,hn₁,hn₂,hn₃]

theorem octadRationalCodeLabel_add_iff (O : Octad) (p q r : RationalCoordinateIndex) :
    octadRationalCodeLabel O r=octadRationalCodeLabel O p+octadRationalCodeLabel O q ↔
      octadRationalLabel O r=octadRationalLabel O p ∆ octadRationalLabel O q := by
  have hsub : octadRationalLabel O p ∆ octadRationalLabel O q ⊆ O.val := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with h | h
    · exact octadRationalLabel_subset O p h.1
    · exact octadRationalLabel_subset O q h.1
  constructor
  · intro h
    apply Finset.ext
    intro i
    by_cases hi : i ∈ O.val
    · have he := congrArg (fun a : octadEvenCode O => a.val ⟨i,hi⟩) h
      change (octadRationalCodeLabel O r).val ⟨i,hi⟩ =
        (octadRationalCodeLabel O p).val ⟨i,hi⟩ + (octadRationalCodeLabel O q).val ⟨i,hi⟩ at he
      simp only [octadRationalCodeLabel_apply] at he
      by_cases hp : i ∈ octadRationalLabel O p <;>
        by_cases hq : i ∈ octadRationalLabel O q <;>
        by_cases hr : i ∈ octadRationalLabel O r <;>
        simp_all [Finset.mem_symmDiff]
    · have hr : i ∉ octadRationalLabel O r := fun h => hi (octadRationalLabel_subset O r h)
      have ht : i ∉ octadRationalLabel O p ∆ octadRationalLabel O q := fun h => hi (hsub h)
      simp [hr,ht]
  · intro h
    apply Subtype.ext
    funext i
    change (octadRationalCodeLabel O r).val i =
      (octadRationalCodeLabel O p).val i + (octadRationalCodeLabel O q).val i
    simp only [octadRationalCodeLabel_apply,h]
    by_cases hp : i.val ∈ octadRationalLabel O p <;>
      by_cases hq : i.val ∈ octadRationalLabel O q <;>
      simp [Finset.mem_symmDiff,hp,hq]

/-- Multiplication obeys symmetric difference in the actual rational grading. -/
theorem octadRationalGrade_product (O : Octad) (S T : Finset Omega)
    (x y : Coordinates) (hx : x ∈ octadRationalGrade O S)
    (hy : y ∈ octadRationalGrade O T) : product x y ∈ octadRationalGrade O (S ∆ T) := by
  classical
  by_cases hx0 : x=0
  · subst x
    have he : product 0 y=0 := map_zero (productLeftMap y)
    rw [he]
    exact (octadRationalGrade O (S ∆ T)).zero_mem
  by_cases hy0 : y=0
  · subst y
    have he : product x 0=0 := map_zero (productRightMap x)
    rw [he]
    exact (octadRationalGrade O (S ∆ T)).zero_mem
  have exists_coordinate (z : Coordinates) (hz : z ≠ 0) :
      ∃ p, rationalCoordinateEquiv z p ≠ 0 := by
    by_contra! hn
    apply hz
    apply rationalCoordinateEquiv.injective
    ext p
    simp [hn p]
  obtain ⟨p,hp⟩ := exists_coordinate x hx0
  obtain ⟨q,hq⟩ := exists_coordinate y hy0
  have hS : octadRationalLabel O p=S := by by_contra h; exact hp (hx p h)
  have hT : octadRationalLabel O q=T := by by_contra h; exact hq (hy q h)
  have hxe := (octadRationalGrade_iff_commonEigenvector O p x).mp (hS.symm ▸ hx)
  have hye := (octadRationalGrade_iff_commonEigenvector O q y).mp (hT.symm ▸ hy)
  have he := (octadCommonEigenvector_iff O _ _).mp (octadCommonEigenvector_product O _ _ x y hxe hye)
  intro r hr
  apply he r
  intro hc
  apply hr
  rw [← hS,← hT]
  exact (octadRationalCodeLabel_add_iff O p q r).mp hc

end Atlas.Fischer
