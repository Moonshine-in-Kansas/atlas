import Atlas.Fischer.DuadOctadDecomposition
import Atlas.Fischer.OctadicMixedAxisProducts
import Atlas.Fischer.OctadicRootMapAxes

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

/-- An octadic root's octad coordinates lie only at its distinguished octad or
at actual octads disjoint from it, independently of calibration and character. -/
theorem octadicRoot_octad_zero_of_support {F : Octad} (Q : OctadCalibration F)
    (χ : OctadicCharacter F) (D : Octad) (hDF : D ≠ F)
    (hd : ¬Disjoint F.val D.val) : octadicRoot Q χ (.inr D)=0 := by
  have ho : signedOctadSupport Q.octadLift=F :=
    (signedOctadSupport_eq_iff _ _).mpr Q.lift_code
  have hb (b : OctadShortenedHyperplane F) :
      D ≠ signedOctadSupport (calibratedHyperplaneLift Q b) := by
    intro h
    exact hd (h.symm ▸ calibratedHyperplaneSupport_disjoint Q b)
  simp only [octadicRoot,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,
    octadicAxisPart_octad_apply,calibratedHyperplaneVector,signedOctadVector,
    xOctad_octad_apply,ho,ite_eq_right hDF,ite_eq_right (hb _),smul_eq_mul,
    mul_zero,Finset.sum_const_zero,zero_add]

theorem duadPair_octadic_octad_coordinate_zero (F G : Octad)
    (hFG : (F.val ∩ G.val).card=2) (Q : OctadCalibration F) (R : OctadCalibration G)
    (χ : OctadicCharacter F) (ψ : OctadicCharacter G) (D : Octad) :
    octadicRoot Q χ (.inr D)=0 ∨ octadicRoot R ψ (.inr D)=0 := by
  have hne : F ≠ G := by
    intro h
    subst G
    rw [Finset.inter_self,octad_size F.val F.property] at hFG
    omega
  have hnd : ¬Disjoint F.val G.val := by
    intro h
    rw [Finset.disjoint_iff_inter_eq_empty] at h
    rw [h] at hFG
    simp at hFG
  by_cases hDF : D=F
  · subst D
    exact Or.inr (octadicRoot_octad_zero_of_support R ψ F hne (fun h => hnd h.symm))
  by_cases hDG : D=G
  · subst D
    exact Or.inl (octadicRoot_octad_zero_of_support Q χ G (Ne.symm hne) hnd)
  by_cases hD : Disjoint F.val D.val
  · have hG : ¬Disjoint G.val D.val := by
      intro hg
      exact octad_not_disjoint_duad_pair F G D hFG (Finset.disjoint_union_right.mpr ⟨hD.symm,hg.symm⟩)
    exact Or.inr (octadicRoot_octad_zero_of_support R ψ D hDG hG)
  · exact Or.inl (octadicRoot_octad_zero_of_support Q χ D hDF hD)

end Atlas.Fischer
