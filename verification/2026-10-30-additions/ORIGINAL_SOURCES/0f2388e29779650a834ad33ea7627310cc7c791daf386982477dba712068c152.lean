import Atlas.LinearGroups.Chevalley.RootData.E6

/-! Height and positivity for the actual integral E6 root pairing.

The sum of the six integral coordinates sends each actual simple root to one.
Applying it to mathlib's integral simple-root expansion identifies the actual
base height. The existing representative exhaustion then identifies the actual
positive roots with the existing 36 representatives.

Verification receipts are recorded separately from the source. -/

noncomputable section
namespace Atlas.Chevalley.TwistedE6
open Atlas.Comparisons.E6Lattice

/-- Height in the actual E6 base is the sum of the original lattice coordinates. -/
theorem e6_height_eq_coordinate_sum (β : E6Data.Root) :
    E6Data.base.height β = ∑ j : Fin 6, β.val j := by
  classical
  obtain ⟨f, _, _, hf⟩ := E6Data.base.exists_root_eq_sum_int β
  have hroot : β.val = ∑ γ ∈ E6Data.base.support, f γ • γ.val := hf
  have hsum : (∑ j : Fin 6, β.val j) = ∑ γ ∈ E6Data.base.support, f γ := by
    rw [hroot]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ hγ
    change γ ∈ Finset.univ.image E6Data.simpleRoot at hγ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hγ
    simp [E6Data.simpleRoot, Pi.single_apply, mul_ite]
  exact (E6Data.base.height_eq_sum hf).trans hsum.symm

/-- Nonnegative coordinates imply positivity because a root has nonzero height. -/
theorem e6_isPos_of_coordinates_nonnegative (β : E6Data.Root)
    (hβ : ∀ j : Fin 6, 0 ≤ β.val j) : E6Data.base.IsPos β := by
  apply (E6Data.base.isPos_iff').2
  rw [e6_height_eq_coordinate_sum]
  exact Finset.sum_nonneg (fun j _ => hβ j)

/-- Each existing norm-one representative is positive for the actual E6 base. -/
theorem e6_representative_isPos (i : Fin 36) :
    E6Data.base.IsPos
      (⟨rootRepresentative i, rootRepresentative_norm i⟩ : E6Data.Root) := by
  exact e6_isPos_of_coordinates_nonnegative _ (E6Data.representative_nonnegative i)

/-- Positivity excludes the negative alternative in the existing root exhaustion. -/
theorem e6_positive_root_exhaustion (β : E6Data.Root) (hβ : E6Data.base.IsPos β) :
    ∃ i : Fin 36, β.val = rootRepresentative i := by
  obtain ⟨i, hi | hi⟩ := root_representative_exhaustion β.val β.property
  · exact ⟨i, hi⟩
  · exfalso
    have hpos : 0 < ∑ j : Fin 6, β.val j := by
      simpa only [e6_height_eq_coordinate_sum] using (E6Data.base.isPos_iff).mp hβ
    have hnonpos : (∑ j : Fin 6, β.val j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j _
      rw [hi, Pi.neg_apply]
      exact neg_nonpos.mpr (E6Data.representative_nonnegative i j)
    exact (not_lt_of_ge hnonpos) hpos

/-- For an actual E6 root, positivity is exactly coordinatewise nonnegativity. -/
theorem e6_isPos_iff_coordinates_nonnegative (β : E6Data.Root) :
    E6Data.base.IsPos β ↔ ∀ j : Fin 6, 0 ≤ β.val j := by
  constructor
  · intro hβ
    obtain ⟨i, hi⟩ := e6_positive_root_exhaustion β hβ
    simpa only [hi] using E6Data.representative_nonnegative i
  · exact e6_isPos_of_coordinates_nonnegative β

/-- The existing representative table enumerates precisely the actual positive roots. -/
theorem e6_isPos_iff_representative (β : E6Data.Root) :
    E6Data.base.IsPos β ↔ ∃ i : Fin 36, β.val = rootRepresentative i := by
  constructor
  · exact e6_positive_root_exhaustion β
  · rintro ⟨i, hi⟩
    apply e6_isPos_of_coordinates_nonnegative β
    simpa only [hi] using E6Data.representative_nonnegative i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Distinctness of the existing 36 vectors; only this finite table is decided. -/
theorem e6_rootRepresentative_injective : Function.Injective rootRepresentative := by
  decide

/-- The actual positive-root subtype, indexed by the existing representative labels. -/
def e6PositiveRootEnumeration (i : Fin 36) :
    {β : E6Data.Root // E6Data.base.IsPos β} :=
  ⟨⟨rootRepresentative i, rootRepresentative_norm i⟩, e6_representative_isPos i⟩

@[simp] theorem e6PositiveRootEnumeration_coordinates (i : Fin 36) :
    (e6PositiveRootEnumeration i).val.val = rootRepresentative i := rfl

theorem e6PositiveRootEnumeration_injective :
    Function.Injective e6PositiveRootEnumeration := by
  intro i j h
  apply e6_rootRepresentative_injective
  exact congrArg (fun β : {β : E6Data.Root // E6Data.base.IsPos β} => β.val.val) h

theorem e6PositiveRootEnumeration_surjective :
    Function.Surjective e6PositiveRootEnumeration := by
  intro β
  obtain ⟨i, hi⟩ := e6_positive_root_exhaustion β.val β.property
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact Subtype.ext hi.symm

theorem e6PositiveRootEnumeration_bijective :
    Function.Bijective e6PositiveRootEnumeration :=
  ⟨e6PositiveRootEnumeration_injective, e6PositiveRootEnumeration_surjective⟩

/-- A bijection with the actual positive-root labels of `E6Data.base`. -/
def e6PositiveRootEquiv : Fin 36 ≃ {β : E6Data.Root // E6Data.base.IsPos β} :=
  Equiv.ofBijective e6PositiveRootEnumeration e6PositiveRootEnumeration_bijective

@[simp] theorem e6PositiveRootEquiv_coordinates (i : Fin 36) :
    (e6PositiveRootEquiv i).val.val = rootRepresentative i := rfl

end Atlas.Chevalley.TwistedE6
