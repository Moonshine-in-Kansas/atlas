import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A group-theoretic derived-subgroup criterion for a two-parameter twisted
root group. No finite-field, ambient order or recognition theorem is used. -/
namespace Atlas
open scoped commutatorElement
variable {F H : Type*} [Field F] [CharP F 2] [Group H]

theorem twistedRoot_mem_commutator_of_scaling (τ : F →+* F)
    (U : F → F → H)
    (hmul : ∀ a b c d, U a b * U c d = U (a+c) (b+d+τ a*c))
    (hinv : ∀ a b, (U a b)⁻¹ = U a (b+a*τ a))
    (t : H) (cscale : F) (hcscale : cscale ≠ 1) (hn : cscale*τ cscale ≠ 1)
    (hscale : ∀ a b, t⁻¹ * U a b * t = U (cscale*a) (cscale*τ cscale*b))
    (a b : F) : U a b ∈ commutator H := by
  have hcscale0 : cscale+1 ≠ 0 := by
    intro h
    apply hcscale
    have he := congrArg (fun x : F => x + 1) h
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using he
  have hn0 : cscale*τ cscale+1 ≠ 0 := by
    intro h
    apply hn
    have he := congrArg (fun x : F => x + 1) h
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using he
  have hcomm (x y : H) : ⁅x,y⁆ ∈ commutator H :=
    Subgroup.commutator_mem_commutator (show x ∈ (⊤ : Subgroup H) from trivial)
      (show y ∈ (⊤ : Subgroup H) from trivial)
  have hc (d : F) : ⁅t⁻¹,U 0 d⁆ = U 0 ((cscale*τ cscale+1)*d) := by
    simp only [commutatorElement_def, inv_inv]
    rw [hscale,hinv,hmul]
    simp only [map_zero, zero_mul, mul_zero, zero_add, add_zero]
    congr 1
    ring
  have hy (d : F) : U 0 d ∈ commutator H := by
    have h := hcomm t⁻¹ (U 0 (d/(cscale*τ cscale+1)))
    rw [hc] at h
    have he : (cscale*τ cscale+1)*(d/(cscale*τ cscale+1)) = d := by field_simp [hn0]
    rwa [he] at h
  have hx (c : F) : ⁅t⁻¹,U c 0⁆ = U ((cscale+1)*c) ((1+τ cscale)*c*τ c) := by
    simp only [commutatorElement_def, inv_inv]
    rw [hscale,hinv,hmul]
    simp only [mul_zero, zero_add, map_mul]
    congr 1 <;> ring
  have hxmem (c : F) : U c 0 ∈ commutator H := by
    let d := c/(cscale+1)
    let e := (1+τ cscale)*d*τ d
    have hd : (cscale+1)*d = c := by dsimp [d]; field_simp [hcscale0]
    have h := hcomm t⁻¹ (U d 0)
    rw [hx,hd] at h
    have hp := (commutator H).mul_mem h (hy e)
    rw [hmul] at hp
    change U (c+0) (e+e+τ c*0) ∈ commutator H at hp
    simpa only [add_zero,mul_zero,CharTwo.add_self_eq_zero] using hp
  have h := (commutator H).mul_mem (hxmem a) (hy b)
  rw [hmul] at h
  simpa only [add_zero,zero_add,mul_zero] using h

end Atlas
