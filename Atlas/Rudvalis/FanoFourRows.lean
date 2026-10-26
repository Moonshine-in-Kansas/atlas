import Atlas.Rudvalis.CoordinateThreePointLinear

namespace Atlas.Rudvalis
local instance fanoFourRowsDecidableEqE : DecidableEq E := Fintype.decidablePiFintype

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
theorem fano_four_rows_alternative (p : Fin 4→Point) (hp : Function.Injective p) :
    (∃a : Point,∃i : Fin 4,dot a.val (p i).val=1 ∧
      ∀j : Fin 4,j≠i → dot a.val (p j).val=0) ∨
    ((pairBasisMatrix (p 0) (p 1) (p 2).val).det=1 ∧
      (p 3).val=(p 0).val+(p 1).val+(p 2).val ∧
      ∃c : Point,(∀i : Fin 4,p i≠c) ∧
        (p 0).val≠(p 3).val ∧ (p 0).val≠c.val ∧
        (p 0).val≠c.val+(p 3).val) := by
  decide +kernel +revert

end Atlas.Rudvalis
