import Atlas.LinearGroups.Symplectic.BinarySixAction
import Atlas.LinearGroups.Symplectic.ProjectiveOrder
import Atlas.LinearGroups.Symplectic.FieldTransport
import Mathlib.GroupTheory.Perm.Sign

noncomputable section
namespace Atlas.Symplectic.BinaryException
local instance : Fintype OddRefinement := Fintype.ofFinite OddRefinement
local instance : DecidableEq OddRefinement := Classical.decEq _
local instance : Nontrivial OddRefinement :=
  Finite.one_lt_card_iff_nontrivial.mp (by rw [card_oddRefinement]; omega)

def permutationHom : Sp 2 K →* Equiv.Perm OddRefinement := MulAction.toPermHom _ _

theorem permutationHom_injective : Function.Injective permutationHom := MulAction.toPerm_injective

theorem card_sp_binary_four : Nat.card (Sp 2 K)=720 := by
  rw [card_sp]
  norm_num [orderNumerator,Finset.prod_range_succ,Nat.card_zmod]

theorem card_six_permutations : Nat.card (Equiv.Perm OddRefinement)=720 := by
  rw [Nat.card_eq_fintype_card,Fintype.card_perm,← Nat.card_eq_fintype_card,card_oddRefinement]
  norm_num [Nat.factorial]

/-- The actual faithful action exhausts the six-point symmetric group. -/
def permutationEquiv : Sp 2 K ≃* Equiv.Perm OddRefinement :=
  MulEquiv.ofBijective permutationHom ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨permutationHom_injective,by rw [card_sp_binary_four,card_six_permutations]⟩)

/-- Sign is applied to the genuine six-quadratic-refinement action. -/
def oddSign : Sp 2 K →* ℤˣ := Equiv.Perm.sign.comp permutationHom

theorem oddSign_surjective : Function.Surjective oddSign :=
  (Equiv.Perm.sign_surjective OddRefinement).comp permutationEquiv.surjective

def signKernel : Subgroup (Sp 2 K) := oddSign.ker

instance signKernel_normal : signKernel.Normal := oddSign.normal_ker

theorem card_signKernel : Nat.card signKernel=360 := by
  have hi : signKernel.index=2 := by
    change oddSign.ker.index=2
    rw [Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective oddSign oddSign_surjective,
      Nat.card_congr Subgroup.topEquiv.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have h := signKernel.card_mul_index
  rw [hi,card_sp_binary_four] at h
  omega

theorem signKernel_ne_bot : signKernel ≠ ⊥ := by
  intro h
  have hc := card_signKernel
  rw [h] at hc
  simp at hc

theorem signKernel_ne_top : signKernel ≠ ⊤ := by
  intro h
  have hc := card_signKernel
  rw [h,Nat.card_congr Subgroup.topEquiv.toEquiv,card_sp_binary_four] at hc
  omega

theorem sp_binary_four_not_simple : ¬ IsSimpleGroup (Sp 2 K) := by
  intro h
  letI := h
  exact signKernel_normal.eq_bot_or_eq_top.elim signKernel_ne_bot signKernel_ne_top

theorem binary_center_eq_bot : Subgroup.center (Sp 2 K)=⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [card_center (by decide)]
  norm_num [Nat.card_zmod]

def projectionEquiv : Sp 2 K ≃* PSp 2 K :=
  MulEquiv.ofBijective projection ⟨by
    apply (MonoidHom.ker_eq_bot_iff (projection (n := 2) (F := K))).mp
    rw [projection_kernel,binary_center_eq_bot],projection_surjective⟩

theorem psp_binary_four_not_simple : ¬ IsSimpleGroup (PSp 2 K) := by
  intro h
  letI := h
  exact sp_binary_four_not_simple projectionEquiv.isSimpleGroup

end Atlas.Symplectic.BinaryException
