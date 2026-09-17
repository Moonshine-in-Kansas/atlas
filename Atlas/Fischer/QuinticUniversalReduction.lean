import Atlas.Fischer.CanonicalTensorReduction
import Atlas.Fischer.QuinticPoints
import Atlas.Fischer.QuinticMixedRows
import Atlas.Fischer.CubicSupportTypes

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

private theorem quintic_point_triple_reduction (p q r : CoordinateIndex)
    (h : IsPointTriple p q r) :
    coordinateQuintic p q r=1002*coordinateCubic p q r := by
  rcases h with ⟨i,j,k,rfl,rfl,rfl⟩
  exact coordinateQuintic_points i j k

private theorem quintic_point_repeated_reduction (p q r : CoordinateIndex) (i : Omega) (O : Octad)
    (h : IsPointRepeatedOctad p q r i O) :
    coordinateQuintic p q r=1002*coordinateCubic p q r := by
  rcases h with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact coordinateQuintic_point_repeated_octad i O
  · exact coordinateQuintic_octad_point_octad O i O
  · exact coordinateQuintic_octads_point O O i

private theorem quintic_binary_triple_solve (a b c z : golay) (h : a+b+c=z) : c=a+b+z := by
  calc
    c = (a+b)+(a+b+c) := by
      have he : (a+b)+(a+b+c)=(a+a)+(b+b)+c := by abel
      rw [he,parkerGolay_add_self,parkerGolay_add_self,zero_add,zero_add]
    _ = a+b+z := by rw [h]

/-- The two actual canonical octad coefficient equations imply the universal
coordinate tensor identity. Every other support family is already proved or
vanishes by the actual cocode character support theorem. -/
theorem coordinateQuintic_universal_of_canonical
    (hS : coordinateQuintic (.inr countingCanonicalD) (.inr countingCanonicalSextetE)
      (.inr countingCanonicalSextetF)=1002*coordinateCubic (.inr countingCanonicalD)
        (.inr countingCanonicalSextetE) (.inr countingCanonicalSextetF))
    (hT : coordinateQuintic (.inr countingCanonicalD) (.inr countingCanonicalTrioE)
      (.inr countingCanonicalTrioF)=1002*coordinateCubic (.inr countingCanonicalD)
        (.inr countingCanonicalTrioE) (.inr countingCanonicalTrioF))
    (p q r : CoordinateIndex) : coordinateQuintic p q r=1002*coordinateCubic p q r := by
  classical
  have htriangle (D E F : Octad)
      (h : octadWord F=octadWord D+octadWord E ∨
        octadWord F=octadWord D+octadWord E+golayOne) :
      coordinateQuintic (.inr D) (.inr E) (.inr F)=
        1002*coordinateCubic (.inr D) (.inr E) (.inr F) := by
    simpa using coordinateQuintic_octad_triangle_of_canonical (1002 : ℚ)
      (by simpa using hS) (by simpa using hT) D E F h
  by_cases hs : IsSevenTypeSupport p q r
  · rcases hs with ⟨hp,_,_⟩ | ⟨hp,_,_⟩ | ⟨hp,_,_,_⟩ |
      ⟨i,O,hp,_⟩ | ⟨i,O,hp,_⟩ |
      ⟨D,E,F,rfl,rfl,rfl,_,_,_,h⟩ | ⟨D,E,F,rfl,rfl,rfl,_,_,_,h⟩
    · exact quintic_point_triple_reduction p q r hp
    · exact quintic_point_triple_reduction p q r hp
    · exact quintic_point_triple_reduction p q r hp
    · exact quintic_point_repeated_reduction p q r i O hp
    · exact quintic_point_repeated_reduction p q r i O hp
    · apply htriangle D E F
      exact Or.inl (by simpa using quintic_binary_triple_solve _ _ _ _ h)
    · exact htriangle D E F (Or.inr (quintic_binary_triple_solve _ _ _ _ h))
  · have hC : coordinateCubic p q r=0 := by
      by_contra hn
      exact hs (coordinateCubic_nonzero_seven_types p q r hn)
    have hK : coordinateQuintic p q r=0 := by
      by_contra hn
      exact hs (coordinateQuintic_nonzero_seven_types p q r hn)
    rw [hC,hK,mul_zero]

end Atlas.Fischer
