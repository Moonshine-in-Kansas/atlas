import Atlas.Conway.IcosianRootPointOrthogonality
import Atlas.Conway.IcosianRootGeometryCard
import Atlas.Combinatorics.RegularUniqueTriangleCount

noncomputable section
namespace Atlas.Conway
open Atlas.Combinatorics

/-- The remaining geometric local obligations imply the exact count of all
actual quaternionic root frames. No group order or transitivity is a premise. -/
theorem icosianRootFrame_card_of_local_geometry
    (hdegree : ∀ p : IcosianRootPoint,
      Nat.card {q : IcosianRootPoint // IcosianRootPointOrthogonal p q}=10)
    (hthird : ∀ p q : IcosianRootPoint,IcosianRootPointOrthogonal p q →
      ∃! r : IcosianRootPoint,IcosianRootPointOrthogonal p r ∧ IcosianRootPointOrthogonal q r) :
    Nat.card IcosianRootFrame=525 := by
  letI : Fintype IcosianRootPoint := Fintype.ofFinite _
  exact regular_unique_triangle_count_315_10 IcosianRootPointOrthogonal
    (fun _ _ => icosianRootPointOrthogonal_symm) icosianRootPointOrthogonal_irrefl
    hthird icosianRootPoint_card hdegree

end Atlas.Conway
