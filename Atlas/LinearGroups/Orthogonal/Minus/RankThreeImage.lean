import Atlas.LinearGroups.Orthogonal.ProjectiveElementary
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeAction
import Atlas.LinearGroups.Orthogonal.Minus.RankThreeIsometry
import Atlas.LinearGroups.Orthogonal.Minus.IntrinsicEven
import Atlas.LinearGroups.Unitary.Family

/-! The actual special unitary exterior-square action on the retained minus form.
Source perfectness places the image in the independently identified intrinsic kernels. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Atlas.Orthogonal.B2Exterior
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def hodgeFixedOrthogonalHom (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.SU F K 4 hdeg →* isometrySubgroup (hodgeFixedForm hdeg) :=
  (hodgeFixedHom hdeg).codRestrict _ (hodgeFixedAction_preserves hdeg)

def rankThreeFullHom (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.SU F K 4 hdeg →* O hdeg 2 :=
  (isometryGroupTransport (rankThreeHodgeIsometry hdeg).symm).toMonoidHom.comp
    (hodgeFixedOrthogonalHom hdeg)

theorem rankThreeFullHom_apply (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.SU F K 4 hdeg) (v : Vector 2 F K) :
    (rankThreeFullHom hdeg g).val v =
      (rankThreeHodgeIsometry hdeg).symm
        (hodgeFixedAction hdeg g (rankThreeHodgeIsometry hdeg v)) := rfl

theorem rankThreeFullHom_intertwine (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.SU F K 4 hdeg) (v : Vector 2 F K) :
    (rankThreeHodgeIsometry hdeg ((rankThreeFullHom hdeg g).val v)).val =
      exteriorMap g.val (rankThreeHodgeIsometry hdeg v).val := by
  rw [rankThreeFullHom_apply,QuadraticMap.IsometryEquiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 400000 in
theorem rankThreeFullHom_mem_elementary (hdeg : Module.finrank F K = 2)
    (g : Atlas.Unitary.SU F K 4 hdeg) : rankThreeFullHom hdeg g ∈ E hdeg 2 := by
  let := Atlas.Unitary.special_perfect_of_good hdeg
    (show Atlas.Unitary.Good 4 (Nat.card F) by simp [Atlas.Unitary.Good])
  let := Group.IsPerfect.range (rankThreeFullHom hdeg)
  have hr : rankThreeFullHom hdeg g ∈ (rankThreeFullHom hdeg).range := ⟨g,rfl⟩
  rw [← Subgroup.commutator_eq_self (H := (rankThreeFullHom hdeg).range)] at hr
  have hc : rankThreeFullHom hdeg g ∈ commutator (O hdeg 2) :=
    Subgroup.commutator_mono le_top le_top hr
  by_cases h2 : (2 : F)=0
  · let : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    rw [← fullDickson_kernel_elementary hdeg 0]
    exact Abelianization.commutator_subset_ker (fullDickson hdeg 0) hc
  · rw [elementary_eq_intrinsic_kernel hdeg 0 h2]
    refine ⟨Abelianization.commutator_subset_ker (determinant (form hdeg 2)) hc, ?_⟩
    have hle : commutator (O hdeg 2) ≤
        (spinorNorm (form hdeg 2) (polar_nondegenerate hdeg 2) h2).ker := by
      rw [commutator_def,Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm ((spinorNorm (form hdeg 2) (polar_nondegenerate hdeg 2) h2) a)
        ((spinorNorm (form hdeg 2) (polar_nondegenerate hdeg 2) h2) b)
    exact hle hc

def rankThreeElementaryHom (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.SU F K 4 hdeg →* E hdeg 2 :=
  (rankThreeFullHom hdeg).codRestrict _ (rankThreeFullHom_mem_elementary hdeg)

def rankThreeProjectiveHom (hdeg : Module.finrank F K = 2) :
    Atlas.Unitary.SU F K 4 hdeg →* ProjectiveElementary (form hdeg 2) :=
  (projectiveElementaryMap (form hdeg 2)).comp (rankThreeElementaryHom hdeg)

end Atlas.Orthogonal.Minus
