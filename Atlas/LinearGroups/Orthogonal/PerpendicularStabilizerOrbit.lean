import Atlas.LinearGroups.Orthogonal.ComplementElementaryLift
import Atlas.LinearGroups.Orthogonal.PerpendicularRootTransport
import Atlas.LinearGroups.Orthogonal.RootFixedSpace
import Atlas.LinearGroups.Orthogonal.ElementaryPairStandard
import Atlas.LinearGroups.Orthogonal.ElementaryFieldTransport
import Atlas.LinearAlgebra.QuadraticNondegenerateTransport

/-! # The elementary point stabilizer on perpendicular singular vectors -/
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V) (he : Q e = 0) (hf : Q f = 0)
  (hef : Q.polarBilin e f = 1)

include he hf hef in
/-- A singular vector perpendicular to e, outside its line, has a nonzero
singular complement coordinate. -/
theorem perpendicular_singular_decomposition (x : V) (hx : Q x = 0)
    (hex : Q.polarBilin e x = 0) (hline : x ∉ Submodule.span F {e}) :
    ∃ c : F, ∃ w : complement Q e f,
      w ≠ 0 ∧ (complementForm Q e f) w = 0 ∧ c • e + w.val = x := by
  let s := split Q e f he hf hef
  have hxe : Q.polarBilin x e = 0 := (polar_swap Q x e).trans hex
  have hs := s.symm_apply_apply x
  change Q.polarBilin x f • e + Q.polarBilin x e • f + (s x).2.val = x at hs
  rw [hxe, zero_smul, add_zero] at hs
  refine ⟨Q.polarBilin x f, (s x).2, ?_, ?_, hs⟩
  · intro hw
    apply hline
    have hzero : (s x).2.val = 0 := congrArg Subtype.val hw
    rw [hzero, add_zero] at hs
    rw [← hs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))
  · have h := form_split Q e f he hf hef x
    change Q x = Q.polarBilin x f * Q.polarBilin x e + Q (s x).2.val at h
    rw [hx, hxe, mul_zero, zero_add] at h
    exact h.symm

include he hf hef in
/-- A complement elementary orbit, followed by a root translation, gives the
actual ambient point-stabilizer orbit. -/
theorem elementary_perpendicular_stabilizer_transport
    (hC : (complementForm Q e f).polarBilin.Nondegenerate)
    (htrans : ∀ u v : complement Q e f, u ≠ 0 → v ≠ 0 →
      (complementForm Q e f) u = 0 → (complementForm Q e f) v = 0 →
      ∃ g : isometrySubgroup (complementForm Q e f),
        g ∈ elementarySubgroup (complementForm Q e f) ∧ g.val u = v)
    (x y : V) (hx : Q x = 0) (hy : Q y = 0)
    (hex : Q.polarBilin e x = 0) (hey : Q.polarBilin e y = 0)
    (hxl : x ∉ Submodule.span F {e}) (hyl : y ∉ Submodule.span F {e}) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val e = e ∧ g.val x = y := by
  obtain ⟨c, w, hw, hqw, hcx⟩ :=
    perpendicular_singular_decomposition Q e f he hf hef x hx hex hxl
  obtain ⟨d, v, hv, hqv, hdy⟩ :=
    perpendicular_singular_decomposition Q e f he hf hef y hy hey hyl
  obtain ⟨k, hk, hkw⟩ := htrans w v hw hv hqw hqv
  let t := complementLift Q e f he hf hef k
  have hte : t.val e = e := complementLift_fix_e Q e f he hf hef k
  have htw : t.val w.val = v.val :=
    (complementLift_apply Q e f he hf hef k w).trans (congrArg Subtype.val hkw)
  obtain ⟨r, hr, hrc⟩ := root_transport_perpendicular_coordinate Q e f he hC v hv c d
  refine ⟨r*t, (elementarySubgroup Q).mul_mem
    (rootSubgroup_le_elementary Q e he hr)
    (complementLift_mem_elementary Q e f he hf hef k hk), ?_, ?_⟩
  · change r.val (t.val e) = e
    rw [hte, rootSubgroup_fixes_direction Q e he r hr]
  · change r.val (t.val x) = y
    rw [← hcx, map_add, map_smul, hte, htw, hrc, hdy]

/-- Nonzero singular-vector elementary transitivity transports through an actual isometry. -/
theorem elementary_singular_transport_of_isometry {W : Type*} [AddCommGroup W] [Module F W]
    (R : QuadraticForm F W) (i : Q.IsometryEquiv R)
    (htrans : ∀ u v : W, u ≠ 0 → v ≠ 0 → R u = 0 → R v = 0 →
      ∃ g : isometrySubgroup R, g ∈ elementarySubgroup R ∧ g.val u = v)
    (u v : V) (hu : u ≠ 0) (hv : v ≠ 0) (hqu : Q u = 0) (hqv : Q v = 0) :
    ∃ g : isometrySubgroup Q, g ∈ elementarySubgroup Q ∧ g.val u = v := by
  let T := semilinearElementaryEquiv (RingEquiv.refl F) i.toLinearEquiv Q R i.map_app
  obtain ⟨k, hk, hku⟩ := htrans (i u) (i v)
    (fun h => hu (i.injective (h.trans (map_zero i).symm)))
    (fun h => hv (i.injective (h.trans (map_zero i).symm)))
    ((i.map_app u).trans hqu) ((i.map_app v).trans hqv)
  let g := T.symm ⟨k, hk⟩
  refine ⟨g.val, g.prop, ?_⟩
  apply i.injective
  have h := T.apply_symm_apply ⟨k, hk⟩
  have ha := congrArg (fun s : elementarySubgroup R => s.val.val (i u)) h
  change i (g.val.val (i.symm (i u))) = k.val (i u) at ha
  rw [i.symm_apply_apply, hku] at ha
  exact ha

/-- In odd type B of rank at least three, the actual elementary e-stabilizer is
transitive on the singular vectors perpendicular to e outside its line. -/
theorem elementaryB_perpendicular_stabilizer_transport (n : ℕ) (h2 : (2 : F) ≠ 0)
    (e f x y : VectorB (n+3) F)
    (he : formB (n+3) F e = 0) (hf : formB (n+3) F f = 0)
    (hef : (formB (n+3) F).polarBilin e f = 1)
    (hx : formB (n+3) F x = 0) (hy : formB (n+3) F y = 0)
    (hex : (formB (n+3) F).polarBilin e x = 0)
    (hey : (formB (n+3) F).polarBilin e y = 0)
    (hxl : x ∉ Submodule.span F {e}) (hyl : y ∉ Submodule.span F {e}) :
    ∃ g : isometrySubgroup (formB (n+3) F), g ∈ elementarySubgroup (formB (n+3) F) ∧
      g.val e = e ∧ g.val x = y := by
  obtain ⟨i⟩ := complement_isometryB e f he hf hef
  apply elementary_perpendicular_stabilizer_transport _ e f he hf hef
    (isometry_between_nondegenerate _ _ i (polarB_nondegenerate h2))
    (fun u v hu hv hqu hqv => elementary_singular_transport_of_isometry _ _ i
      (elementaryB_singular_transport n h2) u v hu hv hqu hqv)
    x y hx hy hex hey hxl hyl

end Atlas.Orthogonal

