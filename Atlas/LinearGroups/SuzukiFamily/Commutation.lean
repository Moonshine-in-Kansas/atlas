import Atlas.LinearGroups.SuzukiFamily.GroupRelations

/-! Reordering identities for the two-cell calculation. -/
noncomputable section
namespace Atlas.SuzukiFamily
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem root_torus_swap (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) (t : Fˣ) :
    rootElement m a b * torusElement m t = torusElement m t *
      rootElement m (theta F m (t:F)*a) ((t:F)^2*theta F m (t:F)*b) := by
  rw [← torus_root_conjugate m hcard t a b,torusElement_inv]
  group

theorem torus_root_swap (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (t : Fˣ) (a b : F) :
    torusElement m t * rootElement m a b =
      rootElement m (theta F m ((t⁻¹:Fˣ):F)*a)
        (((t⁻¹:Fˣ):F)^2*theta F m ((t⁻¹:Fˣ):F)*b) * torusElement m t := by
  rw [← torus_root_conjugate m hcard t⁻¹ a b]
  simp only [inv_inv,torusElement_inv]
  group

theorem torus_weyl_swap (m : ℕ) (t : Fˣ) :
    torusElement m t * weylElement = weylElement * torusElement m t⁻¹ := by
  rw [← weyl_torus_weyl m t]
  simp only [← mul_assoc,weylElement_square,one_mul]
end Atlas.SuzukiFamily
