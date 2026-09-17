import Atlas.LinearGroups.Orthogonal.EvenLift
import Atlas.LinearGroups.Symplectic.Center

/-! # Actual characteristic-two B/C full and projective comparisons -/
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F] [CharP F 2]

@[simp] theorem evenProjection_apply (g : O_B n F) (x : VectorD n F) :
    evenProjection g • x = (g.val (x, 0)).1 :=
  Atlas.Symplectic.ofLinear_apply (evenProjectionLinear g) (evenProjection_preserves g) x

theorem evenProjection_injective : Function.Injective (evenProjection (n := n) (F := F)) := by
  intro g h heq
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hfirst : (g.val x).1 = (h.val x).1 := by
    rw [even_first g, even_first h]
    simpa only [evenProjection_apply] using
      congrArg (fun k : Atlas.Symplectic.Sp n F => k • x.1) heq
  apply Prod.ext hfirst
  have hqg := g.prop x
  have hqh := h.prop x
  rw [formB_apply, hfirst] at hqg
  rw [formB_apply] at hqh
  have hs : (g.val x).2 ^ 2 = (h.val x).2 ^ 2 := add_left_cancel (hqg.trans hqh.symm)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with ht | ht
  · exact ht
  · simpa only [CharTwo.neg_eq] using ht

variable [PerfectRing F 2]

theorem evenProjection_lift (g : Atlas.Symplectic.Sp n F) : evenProjection (evenLift g) = g := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Atlas.Symplectic.Vector n F)
  intro x
  rw [evenProjection_apply]
  exact Atlas.Symplectic.toLinear_apply g x

theorem evenProjection_surjective : Function.Surjective (evenProjection (n := n) (F := F)) :=
  fun g => ⟨evenLift g, evenProjection_lift g⟩

/-- Projection and the quadratic square-root lift give an actual full-group isomorphism. -/
def evenFullEquivSp : O_B n F ≃* Atlas.Symplectic.Sp n F :=
  MulEquiv.ofBijective evenProjection ⟨evenProjection_injective, evenProjection_surjective⟩

/-- In characteristic two, the existing symplectic center is trivial. -/
theorem even_symplectic_center (hn : 0 < n) : Subgroup.center (Atlas.Symplectic.Sp n F) = ⊥ := by
  apply bot_unique
  intro g hg
  obtain ⟨a, ha, hg⟩ := (Atlas.Symplectic.mem_center_iff_scalar hn g).mp hg
  have hone : a = 1 := by
    rcases sq_eq_one_iff.mp ha with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  rw [Subgroup.mem_bot]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Atlas.Symplectic.Vector n F)
  intro x
  rw [hg, hone, one_smul, one_smul]

/-- The full B group in characteristic two is also the existing projective symplectic group. -/
def evenFullEquivPSp (hn : 0 < n) : O_B n F ≃* Atlas.Symplectic.PSp n F :=
  evenFullEquivSp.trans (MulEquiv.ofBijective Atlas.Symplectic.projection
    ⟨by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [Atlas.Symplectic.projection_kernel, even_symplectic_center hn],
      Atlas.Symplectic.projection_surjective⟩)

end Atlas.Orthogonal
