import Atlas.Fischer.BasicCocodeComparison
import Atlas.Fischer.RootMapSymmetry
import Atlas.Fischer.CoordinateHermitianSums

namespace Atlas.Fischer

@[simp] theorem rootMap_zero (r : Coordinates) : rootMap r 0 = 0 :=
  map_zero (rootMapSemilinear r)

/-- Antiunitarity restricted to an actual E-subspace, without any multiplicativity field. -/
def RootMapAntiunitaryOn (r : Coordinates) (S : Submodule Scalar Coordinates) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, hermitian (rootMap r x) (rootMap r y) = star (hermitian x y)

theorem rootMap_invariant_span (r : Coordinates) (s : Set Coordinates)
    (hs : ∀ x ∈ s, rootMap r x ∈ Submodule.span Scalar s) :
    Set.MapsTo (rootMap r) (Submodule.span Scalar s) (Submodule.span Scalar s) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [rootMap_add]
    exact (Submodule.span Scalar s).add_mem ihx ihy
  | smul a x hx ih =>
    rw [rootMap_smul]
    exact (Submodule.span Scalar s).smul_mem _ ih

/-- Pairing checks on the actual spanning vectors suffice for the entire block. -/
theorem rootMap_antiunitary_span (r : Coordinates) (s : Set Coordinates)
    (hs : ∀ x ∈ s, ∀ y ∈ s,
      hermitian (rootMap r x) (rootMap r y) = star (hermitian x y)) :
    RootMapAntiunitaryOn r (Submodule.span Scalar s) := by
  have hg (x : Coordinates) (hx : x ∈ s) : ∀ y ∈ Submodule.span Scalar s,
      hermitian (rootMap r x) (rootMap r y) = star (hermitian x y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hs x hx y hy
    | zero => simp
    | add y z hy hz ihy ihz =>
      rw [rootMap_add, hermitian_add_right, hermitian_add_right, star_add, ihy, ihz]
    | smul a y hy ih =>
      rw [rootMap_smul, hermitian_smul_right, hermitian_smul_right, star_mul, star_star, ih]
      ring
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hg x hx
  | zero => intro y hy; simp
  | add x z hx hz ihx ihz =>
    intro y hy
    rw [rootMap_add, hermitian_add_left, hermitian_add_left, star_add, ihx y hy, ihz y hy]
  | smul a x hx ih =>
    intro y hy
    rw [rootMap_smul, hermitian_smul_left, hermitian_smul_left, star_mul, ih y hy]
    ring

/-- On an invariant block, antiunitarity and the symmetry of the actual root map
imply involutivity. Independent matrix gauges are not used. -/
theorem rootMap_involutive_on_of_antiunitaryOn (r : Coordinates)
    (S : Submodule Scalar Coordinates) (hS : Set.MapsTo (rootMap r) S S)
    (ha : RootMapAntiunitaryOn r S) (x : Coordinates) (hx : x ∈ S) :
    rootMap r (rootMap r x) = x := by
  have hp (y : Coordinates) (hy : y ∈ S) :
      hermitian y (rootMap r (rootMap r x)) = hermitian y x := by
    rw [← rootMap_hermitian_symmetric r (rootMap r x) y, ha x hx y hy, hermitian_star]
  let v := rootMap r (rootMap r x) - x
  have hv : v ∈ S := S.sub_mem (hS (hS hx)) hx
  have hh : hermitian v v = 0 := by
    change hermitian v (rootMap r (rootMap r x) - x) = 0
    rw [hermitian_sub_right, hp v hv, sub_self]
  exact sub_eq_zero.mp ((hermitian_self_eq_zero v).mp hh)

end Atlas.Fischer
