import Atlas.Comparisons.Exceptional.E6.TernaryWitness
import Atlas.Comparisons.Exceptional.E6.PositiveUnitary
import Atlas.LinearGroups.Orthogonal.B2ExteriorComparison

/-! The positive Weyl group maps onto the intrinsic ternary B2 subgroup.
Perfectness forces the image into the derived/determinant-spinor kernel;
simplicity and an explicit nonidentity image give injectivity. -/
noncomputable section
namespace Atlas.Comparisons.E6Lattice
open Atlas.Orthogonal

def positiveTernaryB : positiveWeyl →* O_B 2 (ZMod 3) :=
  intoTernaryB.comp positiveWeyl.subtype

theorem positiveWeyl_perfect : Group.IsPerfect positiveWeyl := by
  let h := Atlas.Unitary.OrderChecks.binary_degree
  letI := Atlas.Unitary.projective_perfect_of_good h
    (show Atlas.Unitary.Good 4 (Nat.card (ZMod 2)) by simp [Atlas.Unitary.Good])
  exact Group.IsPerfect.ofSurjective (f := (positiveWeylUnitaryEquiv h).symm.toMonoidHom)
    (positiveWeylUnitaryEquiv h).symm.surjective

theorem positiveTernaryB_mem_elementary (g : positiveWeyl) :
    positiveTernaryB g ∈ elementarySubgroup (formB 2 (ZMod 3)) := by
  letI := positiveWeyl_perfect
  letI := Group.IsPerfect.range positiveTernaryB
  rw [elementaryB_eq_commutator 0 (by decide : (2 : ZMod 3) ≠ 0)]
  have hr : positiveTernaryB g ∈ positiveTernaryB.range := ⟨g,rfl⟩
  rw [← Subgroup.commutator_eq_self (H := positiveTernaryB.range)] at hr
  exact (Subgroup.commutator_mono (show positiveTernaryB.range ≤ ⊤ from le_top)
    (show positiveTernaryB.range ≤ ⊤ from le_top)) hr

def positiveTernaryElementary : positiveWeyl →* elementarySubgroup (formB 2 (ZMod 3)) :=
  positiveTernaryB.codRestrict _ positiveTernaryB_mem_elementary

theorem positiveTernaryElementary_injective : Function.Injective positiveTernaryElementary := by
  letI := positiveWeyl_simple
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : positiveTernaryElementary.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hm : ternaryWitness ∈ positiveTernaryElementary.ker := by rw [ht]; trivial
    have he : positiveTernaryElementary ternaryWitness = 1 := hm
    exact False.elim (ternaryWitness_orthogonal_ne_one (congrArg Subtype.val he))

theorem ternaryElementary_card : Nat.card (elementarySubgroup (formB 2 (ZMod 3))) = 25920 := by
  rw [← Nat.card_congr (B2Exterior.pspEquivElementary (by decide : (2 : ZMod 3) ≠ 0)).toEquiv,
    Atlas.Symplectic.card_psp (by decide)]
  norm_num [Atlas.Symplectic.orderNumerator,Finset.prod_range_succ,Nat.card_zmod]

theorem positiveTernaryElementary_bijective : Function.Bijective positiveTernaryElementary :=
  positiveTernaryElementary_injective.bijective_of_nat_card_le
    (by rw [positiveWeyl_card,ternaryElementary_card])

/-- The concrete ternary reduction identifies the actual elementary B2(3) carrier. -/
def positiveWeylTernaryElementaryEquiv :
    positiveWeyl ≃* elementarySubgroup (formB 2 (ZMod 3)) :=
  MulEquiv.ofBijective positiveTernaryElementary positiveTernaryElementary_bijective

/-- Compose the retained exterior-square B2/C2 map, without a second recognition argument. -/
def positiveWeylSymplecticEquiv : positiveWeyl ≃* Atlas.Symplectic.PSp 2 (ZMod 3) :=
  positiveWeylTernaryElementaryEquiv.trans
    (B2Exterior.pspEquivElementary (by decide : (2 : ZMod 3) ≠ 0)).symm

end Atlas.Comparisons.E6Lattice
