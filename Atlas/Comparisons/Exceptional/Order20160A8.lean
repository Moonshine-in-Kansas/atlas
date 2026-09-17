import Atlas.Comparisons.Exceptional.DeletedEightFaithful
import Atlas.Comparisons.Classical.Orthogonal
import Atlas.LinearGroups.Orthogonal.FullDicksonD
import Atlas.LinearGroups.Orthogonal.IsometryTransport
import Atlas.GroupTheory.NonabelianSimplePerfect
import Atlas.Families.Alternating.Basic
import Atlas.LinearGroups.PSLFamily

/-! The actual A8 action on the deleted quadratic module realizes split D3(2). -/
noncomputable section
namespace Atlas.Comparisons.Exceptional
open Atlas.Codes Atlas.Orthogonal
open scoped MatrixGroups

namespace DeletedEight

def orthogonalHom : Equiv.Perm (Fin 8) →* O_DPlus 3 Bit :=
  (isometryGroupTransport splitIsometry.symm).toMonoidHom.comp permutationHom

theorem orthogonalHom_injective : Function.Injective orthogonalHom :=
  (isometryGroupTransport splitIsometry.symm).injective.comp permutationHom_injective

abbrev A := alternatingGroup (Fin 8)
def alternatingHom : A →* O_DPlus 3 Bit := orthogonalHom.comp (alternatingGroup (Fin 8)).subtype

theorem alternatingHom_elementary (g : A) : alternatingHom g ∈ elementarySubgroup (formD 3 Bit) := by
  letI := Atlas.Families.Alternating.isSimpleGroup 8 (by change 5 ≤ 8; decide)
  letI := Atlas.GroupTheory.nonabelian_simple_perfect A
    (Atlas.Families.Alternating.exists_mul_ne_mul 8 (by decide))
  let f := (fullDicksonD (F := Bit) 0).comp alternatingHom
  have h := Abelianization.commutator_subset_ker f
  rw [Group.IsPerfect.commutator_eq_top] at h
  have hg : g ∈ f.ker := h (Subgroup.mem_top g)
  rw [← fullDicksonD_kernel_elementary (F := Bit) 0]
  exact hg

def elementaryHom : A →* elementarySubgroup (formD 3 Bit) :=
  alternatingHom.codRestrict _ alternatingHom_elementary

theorem elementaryHom_injective : Function.Injective elementaryHom := by
  intro g h he
  apply Subtype.ext
  apply orthogonalHom_injective
  exact congrArg Subtype.val he

theorem binary_scalar_eq_bot : elementaryScalarSubgroup (formD 3 Bit) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro g ⟨c,hc,hg⟩
  have hc1 : c = 1 := by
    rcases bit_cases c with h | h
    · simp [h] at hc
    · exact h
  change g = 1
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simpa [hc1] using hg x

theorem projection_injective : Function.Injective (projectiveElementaryMap (formD 3 Bit)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [projectiveElementaryMap_kernel, binary_scalar_eq_bot]

def projectiveHom : A →* ProjectiveElementary (formD 3 Bit) :=
  (projectiveElementaryMap _).comp elementaryHom

theorem projectiveHom_injective : Function.Injective projectiveHom :=
  projection_injective.comp elementaryHom_injective

end DeletedEight

theorem psl4Two_card : Nat.card PSL(4,ZMod 2) = 20160 := by
  rw [Atlas.card_psl_factor (F := ZMod 2) 4]
  norm_num [Nat.card_eq_fintype_card, Finset.prod_Icc_succ_top]

theorem alt8_card : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The faithful deleted-module action onto the actual split D3 projective group. -/
def alt8EquivD3Two : alternatingGroup (Fin 8) ≃* ProjectiveElementary (formD 3 (ZMod 2)) :=
  MulEquiv.ofBijective DeletedEight.projectiveHom
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨DeletedEight.projectiveHom_injective, by
      rw [Nat.card_congr (Atlas.Comparisons.Classical.d3EquivA3 (F := ZMod 2)).toEquiv,
        psl4Two_card, alt8_card]⟩)

/-- Exceptional A3(2)/A8 comparison, induced by the actual binary quadratic module. -/
def psl4TwoEquivAlt8 : PSL(4,ZMod 2) ≃* alternatingGroup (Fin 8) :=
  (Atlas.Comparisons.Classical.d3EquivA3 (F := ZMod 2)).symm.trans alt8EquivD3Two.symm

end Atlas.Comparisons.Exceptional
