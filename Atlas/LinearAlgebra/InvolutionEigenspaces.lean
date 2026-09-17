import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic

/-! # The two actual eigenspaces of a linear involution -/
noncomputable section
namespace Atlas.LinearInvolution
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

def plus (t : V →ₗ[F] V) : Submodule F V := LinearMap.ker (t - LinearMap.id)
def minus (t : V →ₗ[F] V) : Submodule F V := LinearMap.ker (t + LinearMap.id)

@[simp] theorem mem_plus (t : V →ₗ[F] V) (x : V) : x ∈ plus t ↔ t x = x := by
  simp [plus,LinearMap.mem_ker,sub_eq_zero]
@[simp] theorem mem_minus (t : V →ₗ[F] V) (x : V) : x ∈ minus t ↔ t x = -x := by
  simp [minus,LinearMap.mem_ker,add_eq_zero_iff_eq_neg]

theorem isCompl (t : V →ₗ[F] V) (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    IsCompl (plus t) (minus t) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    rw [mem_plus] at hx
    rw [mem_minus] at hy
    have he : x = -x := hx.symm.trans hy
    have hz : (2 : F) • x = 0 := by
      calc
        _ = x + x := two_smul F x
        _ = x + -x := congrArg (fun z => x + z) he
        _ = 0 := add_neg_cancel x
    exact (smul_eq_zero.mp hz).resolve_left h2
  · rw [codisjoint_iff,eq_top_iff]
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨(2 : F)⁻¹ • (x + t x), ?_, (2 : F)⁻¹ • (x - t x), ?_, ?_⟩
    · rw [mem_plus]
      simp only [map_smul,map_add,ht x]
      rw [add_comm]
    · rw [mem_minus]
      simp only [map_smul,map_sub,ht x]
      rw [← smul_neg, neg_sub]
    · rw [← smul_add]
      have he : (x + t x) + (x - t x) = (2 : F) • x := by rw [two_smul]; abel
      rw [he,smul_smul,inv_mul_cancel₀ h2,one_smul]

/-- Addition gives the actual direct-sum coordinates of the involution. -/
def decomposition (t : V →ₗ[F] V) (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    (plus t × minus t) ≃ₗ[F] V := Submodule.prodEquivOfIsCompl _ _ (isCompl t ht h2)

theorem orthogonal (b : LinearMap.BilinForm F V) (t : V →ₗ[F] V)
    (hb : ∀ x y, b (t x) (t y) = b x y) (h2 : (2 : F) ≠ 0)
    (x : plus t) (y : minus t) : b x.val y.val = 0 := by
  have hx := (mem_plus t x.val).mp x.prop
  have hy := (mem_minus t y.val).mp y.prop
  have he := hb x.val y.val
  rw [hx,hy,map_neg] at he
  have hz : (2 : F) * b x.val y.val = 0 := by linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left h2

theorem decomposition_action (t : V →ₗ[F] V) (ht : Function.Involutive t)
    (h2 : (2 : F) ≠ 0) (x : plus t × minus t) :
    t (decomposition t ht h2 x) = x.1.val - x.2.val := by
  change t (x.1.val + x.2.val) = _
  rw [map_add,(mem_plus _ _).mp x.1.prop,(mem_minus _ _).mp x.2.prop,sub_eq_add_neg]
end Atlas.LinearInvolution
