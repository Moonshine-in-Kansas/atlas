import Atlas.LinearGroups.Chevalley.RootData.ClassicalDAxisRepresentatives
import Atlas.LinearGroups.Chevalley.RootData.ClassicalDFunctionalOrbit
import Atlas.LinearGroups.Chevalley.RootData.ParabolicCosetDecomposition

/-! Minimal RIGHT-parabolic representatives in actual type D, rank at least
three. The inverse of a shortest signed-row word has the correct right-coset
orientation. The equal-distance fork labels remain separately indexed. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDParabolic
open Classical ClassicalData RootData

private def pathWord (n : ℕ) (c : Fin (n + 3) × Bool) :
    List (baseD (n + 1)).support :=
  (ClassicalDAxis.exists_reduced_coordinate_word (n + 1) c).choose

private theorem pathWord_spec (n : ℕ) (c : Fin (n + 3) × Bool) :
    IsReducedRootWord (pairingD (n + 3)) (baseD (n + 1)) (pathWord n c) ∧
      (pathWord n c).length = ClassicalDAxis.distance (n + 1) c ∧
      ∀ β : DRoot (n + 3),
        ((rootWeylWord (pairingD (n + 3)) (baseD (n + 1)) (pathWord n c)).val β).val 0 =
          ClassicalDAxis.coordinate (n + 1) c β :=
  (ClassicalDAxis.exists_reduced_coordinate_word (n + 1) c).choose_spec

/-- Inversion converts the explicit pullback-row word into a right-coset representative. -/
def coordinateRepresentative (n : ℕ) (c : Fin (n + 3) × Bool) :
    (pairingD (n + 3)).weylGroupToPerm.range :=
  (rootWeylWord (pairingD (n + 3)) (baseD (n + 1)) (pathWord n c))⁻¹

theorem coordinateRepresentative_inverse_row (n : ℕ) (c : Fin (n + 3) × Bool)
    (β : DRoot (n + 3)) :
    (((coordinateRepresentative n c)⁻¹).val β).val 0 =
      ClassicalDAxis.coordinate (n + 1) c β := by
  simpa only [coordinateRepresentative, inv_inv] using (pathWord_spec n c).2.2 β

theorem coordinateRepresentative_length (n : ℕ) (c : Fin (n + 3) × Bool) :
    rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) (coordinateRepresentative n c) =
      ClassicalDAxis.distance (n + 1) c := by
  rw [coordinateRepresentative, rootWeylLength_inv]
  exact (pathWord_spec n c).1.trans (pathWord_spec n c).2.1

/-- The exact length-additive parabolic split forces the tail factor to be
trivial: its inverse fixes the first coordinate and cannot shorten the row path. -/
theorem coordinateRepresentative_minimal (n : ℕ) (c : Fin (n + 3) × Bool) :
    ∀ i ∈ J n, (baseD (n + 1)).IsPos ((coordinateRepresentative n c).val i.val) := by
  let p := (rootParabolicProductEquiv (pairingD (n + 3)) (baseD (n + 1)) (J n)).symm
    (coordinateRepresentative n c)
  have hp : p.1.val * p.2.val = coordinateRepresentative n c :=
    (rootParabolicProductEquiv (pairingD (n + 3)) (baseD (n + 1)) (J n)).apply_symm_apply _
  have hfix := (mem_parabolic_iff_preserves_first n p.2.val⁻¹).mp
    ((rootParabolicSubgroup (pairingD (n + 3)) (baseD (n + 1)) (J n)).inv_mem p.2.property)
  have hrow : ∀ β : DRoot (n + 3), ((p.1.val⁻¹).val β).val 0 =
      ClassicalDAxis.coordinate (n + 1) c β := by
    intro β
    have h := coordinateRepresentative_inverse_row n c β
    rw [← hp, mul_inv_rev] at h
    change ((p.2.val⁻¹).val ((p.1.val⁻¹).val β)).val 0 = _ at h
    rwa [hfix] at h
  have hbound := ClassicalDAxis.distance_le_rootWeylLength (n + 1) p.1.val⁻¹ c hrow
  rw [rootWeylLength_inv] at hbound
  change ClassicalDAxis.distance (n + 1) c ≤
    rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) p.1.val at hbound
  have hlen := rootParabolicProductEquiv_length (pairingD (n + 3)) (baseD (n + 1)) (J n) p
  change rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) (p.1.val * p.2.val) = _ at hlen
  rw [hp, coordinateRepresentative_length] at hlen
  have hv0 : rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) p.2.val = 0 := by omega
  have hv1 := (rootWeylLength_eq_zero_iff (pairingD (n + 3)) (baseD (n + 1)) p.2.val).mp hv0
  have hx : p.1.val = coordinateRepresentative n c := by simpa only [hv1, mul_one] using hp
  simpa only [hx] using p.1.property

def coordinateRepresentativeMap (n : ℕ) : (Fin (n + 3) × Bool) →
    rootParabolicRepresentatives (pairingD (n + 3)) (baseD (n + 1)) (J n) :=
  fun c => ⟨coordinateRepresentative n c, coordinateRepresentative_minimal n c⟩

/-- Labels, rather than their distances, index the representatives. In particular
the two different middle representatives are not collapsed. -/
theorem coordinateRepresentativeMap_bijective (n : ℕ) :
    Function.Bijective (coordinateRepresentativeMap n) := by
  constructor
  · intro c d h
    have he : coordinateRepresentative n c = coordinateRepresentative n d := congrArg Subtype.val h
    apply ClassicalDAxis.coordinate_injective (n + 1)
    funext β
    rw [← coordinateRepresentative_inverse_row, ← coordinateRepresentative_inverse_row, he]
  · intro x
    obtain ⟨c, hc⟩ := rootCoordinate_weyl n x.val⁻¹ (0, true)
    have hxrow : ∀ β : DRoot (n + 3), ((x.val⁻¹).val β).val 0 =
        ClassicalDAxis.coordinate (n + 1) c β := by
      intro β
      simpa only [rootCoordinate, ClassicalDAxis.coordinate, Integral.Minuscule.TypeD.sign,
        Bool.true_eq, ↓reduceIte, one_mul] using hc β
    have hfix : ∀ β : DRoot (n + 3),
        (((coordinateRepresentative n c)⁻¹ * x.val).val β).val 0 = β.val 0 := by
      intro β
      change (((coordinateRepresentative n c)⁻¹).val (x.val.val β)).val 0 = _
      rw [coordinateRepresentative_inverse_row, ← hxrow]
      change (x.val.val.symm (x.val.val β)).val 0 = _
      rw [x.val.val.symm_apply_apply]
    have he := rootWeyl_parabolic_minimal_unique (pairingD (n + 3)) (baseD (n + 1)) (J n)
      (coordinateRepresentative n c) x.val (coordinateRepresentative_minimal n c) x.property
      ((mem_parabolic_iff_preserves_first n _).mpr hfix)
    exact ⟨c, Subtype.ext he⟩

/-- The 2r actual minimal right-parabolic representatives, with the two middle
points kept distinct. This is a set equivalence, not a group isomorphism. -/
def coordinateRepresentativeEquiv (n : ℕ) : (Fin (n + 3) × Bool) ≃
    rootParabolicRepresentatives (pairingD (n + 3)) (baseD (n + 1)) (J n) :=
  Equiv.ofBijective (coordinateRepresentativeMap n) (coordinateRepresentativeMap_bijective n)

theorem coordinateRepresentativeEquiv_length (n : ℕ) (c : Fin (n + 3) × Bool) :
    rootWeylLength (pairingD (n + 3)) (baseD (n + 1)) (coordinateRepresentativeEquiv n c).val =
      ClassicalDAxis.distance (n + 1) c :=
  coordinateRepresentative_length n c

end Atlas.Chevalley.ClassicalDParabolic
