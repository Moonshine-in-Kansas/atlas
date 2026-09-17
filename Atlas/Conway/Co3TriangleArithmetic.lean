import Atlas.Conway.Co3TriangleParameters

namespace Atlas.Conway
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem co3_triangle_ambient_divisibility (T : Finset (Fin 8)) (h0 : 0 ∈ T) (h3 : 3 ∈ T)
    (hd : (∑ t ∈ T, co3TriangleSize t) ∣ 8315553613086720000) :
    T = {0,1,3} ∨ T = Finset.univ := by
  revert hd h3 h0 T
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem co3_triangle_block_divisibility (T : Finset (Fin 8)) (h0 : 0 ∈ T)
    (hd : (∑ t ∈ T, co3TriangleSize t) ∣ 48600) :
    T = {0} ∨ T = {0,1,3} ∨ T = Finset.univ := by
  revert hd h0 T
  decide +kernel

end Atlas.Conway
