import Atlas.Rudvalis.FullPointStabilizer
import Atlas.Rudvalis.PointFixingTranslations

namespace Atlas.Rudvalis
local instance : DecidableEq E := Fintype.decidablePiFintype

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- A binary three-dimensional linear map preserving every one-dimensional subspace is scalar. -/
theorem binaryMatrix_fix_lines_scalar (A : BinaryMatrix)
    (h : ∀p : Point,matrixAt A p.val=0 ∨ matrixAt A p.val=p.val) : A=0 ∨ A=1 := by
  decide +kernel +revert

theorem code_fix_coordinateCross_block (g : codeGroup)
    (hg : ∀i : Coordinate,g • coordinateCross i=coordinateCross i) :
    codeBlockLinearHom g=1 := by
  have hp (i : Coordinate) : (g.val.right i).1=i.1 := by
    apply coordinateCross_row_of_eq
    rw [←coordinateCross_action]
    exact hg i
  apply LinearEquiv.ext
  intro x
  by_cases hx : x=0
  · subst x;exact map_zero _
  · exact (codeBlockLinear_coordinates g (⟨x,hx⟩,0)).trans (congrArg Subtype.val (hp (⟨x,hx⟩,0)))

/-- Pointwise fixation of the Gaussian coordinate frame leaves only the identity or I permutation. -/
theorem code_fix_coordinateCross_permutation (g : codeGroup)
    (hg : ∀i : Coordinate,g • coordinateCross i=coordinateCross i) :
    g.val.right=1 ∨ g.val.right=codeI.val.right := by
  have hb : codePermutationHom g∈binaryBlockLinearHom.ker := code_fix_coordinateCross_block g hg
  rw [binaryBlockLinearHom_kernel_translations] at hb
  obtain ⟨A,hA⟩ := hb
  have he : coordinateTranslation A.toAdd=g.val.right := congrArg Subtype.val hA
  have hp (p : Point) : matrixAt A.toAdd p.val=0 ∨ matrixAt A.toAdd p.val=p.val := by
    have hx := hg (p,0)
    rw [coordinateCross_action,←he] at hx
    rcases (coordinateCross_eq_iff _ _).mp hx.symm with h|h
    · left
      have hh := congrArg Prod.snd h
      change 0=0+matrixAt A.toAdd p.val at hh
      simpa only [zero_add] using hh.symm
    · right
      rw [codeI_coordinate] at h
      have hh := congrArg Prod.snd h
      change 0+p.val=0+matrixAt A.toAdd p.val at hh
      simpa only [zero_add] using hh.symm
  rcases binaryMatrix_fix_lines_scalar A.toAdd hp with hA|hA
  · left
    rw [←he,hA]
    apply Equiv.ext
    intro z
    change (z.1,z.2+matrixAt 0 z.1.val)=z
    have hz : matrixAt (0:BinaryMatrix) z.1.val=0 := Matrix.zero_mulVec _
    rw [hz,add_zero]
  · right
    rw [←he,hA]
    apply Equiv.ext
    intro z
    rw [codeI_coordinate]
    change (z.1,z.2+matrixAt 1 z.1.val)=(z.1,z.2+z.1.val)
    have hz : matrixAt (1:BinaryMatrix) z.1.val=z.1.val := Matrix.one_mulVec _
    rw [hz]

end Atlas.Rudvalis
