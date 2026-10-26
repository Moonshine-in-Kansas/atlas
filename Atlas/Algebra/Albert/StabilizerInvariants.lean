import Atlas.Algebra.Albert.ScalarExtension

/-! Recovering the quadratic structure by coefficients, in every characteristic. -/
noncomputable section
namespace Atlas.Albert
variable {F : Type*} [CommRing F]

theorem stabilizer_trace_quadraticTrace (g : polynomialStabilizer (F := F)) (x : Carrier F) :
    trace (g.val x) = trace x ∧ quadraticTrace (g.val x) = quadraticTrace x := by
  let c : F →+* Polynomial F := Polynomial.C
  have h := scalarExtension_norm g c (unit + (Polynomial.X : Polynomial F) • map c x)
  rw [_root_.map_add, map_smul, scalarExtension_unit, scalarExtension_map] at h
  simp only [norm_unit_add_smul, trace_map, quadraticTrace_map, norm_map] at h
  constructor
  · have h1 := congrArg (fun p : Polynomial F => p.coeff 1) h
    simpa [c, Polynomial.coeff_add] using h1
  · have h2 := congrArg (fun p : Polynomial F => p.coeff 2) h
    simpa [c, Polynomial.coeff_add] using h2

theorem stabilizer_trace (g : polynomialStabilizer (F := F)) (x : Carrier F) :
    trace (g.val x) = trace x := (stabilizer_trace_quadraticTrace g x).1

theorem stabilizer_quadraticTrace (g : polynomialStabilizer (F := F)) (x : Carrier F) :
    quadraticTrace (g.val x) = quadraticTrace x := (stabilizer_trace_quadraticTrace g x).2

theorem stabilizer_tracePairing (g : polynomialStabilizer (F := F)) (x y : Carrier F) :
    tracePairing (g.val x) (g.val y) = tracePairing x y := by
  simp only [tracePairing, ← _root_.map_add, stabilizer_trace, stabilizer_quadraticTrace]

theorem stabilizer_directionalCubic (g : polynomialStabilizer (F := F)) (x y : Carrier F) :
    directionalCubic (g.val x) (g.val y) = directionalCubic x y := by
  have h := scalarExtension_norm g (Polynomial.C : F →+* Polynomial F)
    (map Polynomial.C x + (Polynomial.X : Polynomial F) • map Polynomial.C y)
  rw [_root_.map_add, map_smul, scalarExtension_map, scalarExtension_map] at h
  exact h

theorem stabilizer_adjoint_pairing (g : polynomialStabilizer (F := F)) (x y : Carrier F) :
    tracePairing (adjoint (g.val x)) (g.val y) = tracePairing (adjoint x) y := by
  have h := congrArg (fun p : Polynomial F => p.coeff 1) (stabilizer_directionalCubic g x y)
  simpa only [directionalCubic_coeff_one] using h

theorem stabilizer_adjoint (g : polynomialStabilizer (F := F)) (x : Carrier F) :
    adjoint (g.val x) = g.val (adjoint x) := by
  apply sub_eq_zero.mp
  apply tracePairing_nondegenerate
  intro z
  obtain ⟨y, rfl⟩ := g.val.surjective z
  have h := stabilizer_adjoint_pairing g x y
  rw [← stabilizer_tracePairing g (adjoint x) y] at h
  have hs : ∀ u v w : Carrier F,
      tracePairing (u-v) w = tracePairing u w - tracePairing v w := by
    intro u v w
    have hh := tracePairing_add_left u (-v) w
    rw [← neg_one_smul F v, tracePairing_smul_left] at hh
    simpa [sub_eq_add_neg] using hh
  rw [hs, h, sub_self]

theorem stabilizer_cross (g : polynomialStabilizer (F := F)) (x y : Carrier F) :
    cross (g.val x) (g.val y) = g.val (cross x y) := by
  simp only [cross, ← _root_.map_add, stabilizer_adjoint, map_sub]

end Atlas.Albert
