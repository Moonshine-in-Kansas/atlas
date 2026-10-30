import Atlas.LinearGroups.SuzukiFamily.ExactStabilizer
import Atlas.LinearGroups.ReeF4.RootGroupUnits

/-!
Source-only, uncompiled. In the actual generated Suzuki matrix group, the
stabilizer of the vector infinityVector is the actual two-parameter root group.
The existing projective stabilizer gives root times torus; vector fixation
removes the torus through the already proved thetaNormEquiv on field units.
No group-order or simplicity theorem is used.
-/

noncomputable section
namespace Atlas.ReeF4
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem suzuki_shortForm_infinityVector (m : ℕ) (a b : F) (t : Fˣ) :
    SuzukiFamily.matrix (SuzukiFamily.shortForm m a b t) *ᵥ
        (SuzukiFamily.infinityVector : SuzukiFamily.Vector F) =
      (((t⁻¹ : Fˣ) : F) * theta F m ((t⁻¹ : Fˣ) : F)) •
        SuzukiFamily.infinityVector := by
  have ht : SuzukiFamily.h m t *ᵥ
      (SuzukiFamily.infinityVector : SuzukiFamily.Vector F) =
      (((t⁻¹ : Fˣ) : F) * theta F m ((t⁻¹ : Fˣ) : F)) •
        SuzukiFamily.infinityVector := by
    funext i
    fin_cases i <;>
      simp [SuzukiFamily.h, SuzukiFamily.infinityVector, Matrix.mulVec_diagonal,
        Pi.smul_apply, smul_eq_mul]
  rw [SuzukiFamily.shortForm, SuzukiFamily.matrix_mul, ← Matrix.mulVec_mulVec,
    SuzukiFamily.matrix_torus, SuzukiFamily.matrix_root, ht, Matrix.mulVec_smul,
    SuzukiFamily.root_infinity_vector]

/-- The group membership is in SuzukiFamily.Group, not in the whole symplectic group. -/
theorem suzuki_infinityVector_fixer_iff_root {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (s : SuzukiFamily.Group F m) :
    SuzukiFamily.matrix s.val *ᵥ
        (SuzukiFamily.infinityVector : SuzukiFamily.Vector F) = SuzukiFamily.infinityVector ↔
      ∃ a b : F, s.val = SuzukiFamily.rootElement m a b := by
  constructor
  · intro hfix
    have hp : SuzukiFamily.pointLeft s.val SuzukiFamily.infinityPoint =
        SuzukiFamily.infinityPoint := by
      change Projectivization.mk F
        (SuzukiFamily.matrix s.val *ᵥ SuzukiFamily.infinityVector) _ =
          Projectivization.mk F SuzukiFamily.infinityVector _
      simp only [hfix]
    obtain ⟨a,b,t,hs⟩ :=
      (SuzukiFamily.fixes_infinity_iff_short m hcard s.val s.property).mp hp
    rw [hs, suzuki_shortForm_infinityVector] at hfix
    have hc : (((t⁻¹ : Fˣ) : F) * theta F m ((t⁻¹ : Fˣ) : F)) = 1 := by
      simpa [SuzukiFamily.infinityVector, Pi.smul_apply, smul_eq_mul] using
        congrFun hfix 3
    have hn : thetaNormEquiv hcard t⁻¹ = 1 := Units.ext hc
    have hi : t⁻¹ = 1 := (thetaNormEquiv hcard).injective (by
      simpa only [map_one] using hn)
    have ht : t = 1 := inv_eq_one.mp hi
    refine ⟨a,b,?_⟩
    simpa only [SuzukiFamily.shortForm, ht, SuzukiFamily.torusElement_one, mul_one] using hs
  · rintro ⟨a,b,hs⟩
    rw [hs, SuzukiFamily.matrix_root, SuzukiFamily.root_infinity_vector]

end Atlas.ReeF4
