import Atlas.Comparisons.Exceptional.G2Binary.QuadraticPoints
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.GroupAction.Hom

namespace Atlas.Comparisons.G2Binary
open Atlas.SplitOctonion

/-- Octonion automorphisms preserve the two roots in each quadratic subalgebra. -/
theorem automorphism_partner (g : Automorphism K) (x : V) :
    g.val (partner x) = partner (g.val x) := by
  simp [partner]

theorem automorphism_root (g : Automorphism K) (x : V) (hx : IsQuadraticRoot x) :
    IsQuadraticRoot (g.val x) := by
  simpa only [IsQuadraticRoot, automorphism_trace, automorphism_norm] using hx

/-- Normalizing before applying an automorphism has no effect on its point image. -/
theorem normalize_automorphism_normalize (g : Automorphism K) (x : V) :
    normalize (g.val (normalize x)) = normalize (g.val x) := by
  rcases normalize_cases x with h | h
  · rw [h]
  · rw [h, automorphism_partner, normalize_partner]

instance quadraticPointAction : MulAction (Automorphism K) QuadraticPoint where
  smul g x := ⟨normalize (g.val x.val),
    (normalize_geometry (g.val x.val)).1 (automorphism_root g x.val x.property.1)⟩
  one_smul x := by
    apply Subtype.ext
    change normalize x.val = x.val
    simp [normalize, x.property.2]
  mul_smul g h x := by
    apply Subtype.ext
    change normalize (g.val (h.val x.val)) = normalize (g.val (normalize (h.val x.val)))
    exact (normalize_automorphism_normalize g (h.val x.val)).symm

/-- The resulting homomorphism uses the full original octonion group. -/
def quadraticPointRepresentation : Automorphism K →* Equiv.Perm QuadraticPoint :=
  MulAction.toPermHom _ _

theorem quadraticPoint_action_eq_iff (g : Automorphism K) (x y : QuadraticPoint) :
    g • x = y ↔ g.val x.val = y.val ∨ g.val x.val = partner y.val := by
  rw [Subtype.ext_iff]
  change normalize (g.val x.val) = y.val ↔ _
  have hy : normalize y.val = y.val := by simp [normalize,y.property.2]
  rw [← hy, normalize_eq_iff]
  rw [hy]

end Atlas.Comparisons.G2Binary
