import Atlas.LinearGroups.Orthogonal.RootFixedSpace

/-! # The full linear-isometry centralizer of an elementary orthogonal group is scalar -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem centralizer_siegel_commutes (z : isometrySubgroup Q)
    (hz : ∀ g ∈ elementarySubgroup Q, g*z = z*g)
    (u v : V) (hu : Q u = 0) (huv : Q.polarBilin u v = 0) (x : V) :
    z.val (siegel Q u v x) = (siegelElement Q u v hu huv).val (z.val x) := by
  exact (congrArg (fun k : isometrySubgroup Q => k.val x)
    (hz (siegelElement Q u v hu huv) (siegelElement_mem Q u v hu huv))).symm

theorem centralizer_isotropic_parameter (z : isometrySubgroup Q)
    (hz : ∀ g ∈ elementarySubgroup Q, g*z = z*g)
    (e f : V) (he : Q e = 0) (hef : Q.polarBilin e f = 1)
    (a : complement Q e f) (ha : Q a.val = 0) (d : F) (hdf : z.val f = d • f) :
    z.val a.val = d • a.val := by
  have hea : Q.polarBilin e a.val = 0 := (polar_swap Q e a.val).trans a.prop.1
  have hfa : Q.polarBilin f a.val = 0 := (polar_swap Q f a.val).trans a.prop.2
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  have hv : siegel Q e a.val f = f - a.val := by
    simp only [siegel, hfa, hfe, ha, zero_smul, add_zero, one_smul, zero_mul, sub_zero]
  have h := centralizer_siegel_commutes Q z hz e a.val he hea f
  rw [hv, map_sub, hdf, map_smul] at h
  change d • f - z.val a.val = d • siegel Q e a.val f at h
  rw [hv, smul_sub] at h
  exact sub_right_inj.mp h

/-- Two actual perpendicular hyperbolic planes suffice; no order or simplicity is assumed. -/
theorem elementary_centralizer_scalar (hQ : Q.polarBilin.Nondegenerate)
    (e f : V) (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)
    (a b : complement Q e f) (ha : Q a.val = 0) (hab : Q.polarBilin a.val b.val = 1)
    (z : isometrySubgroup Q) (hz : ∀ g ∈ elementarySubgroup Q, g*z = z*g) :
    ∃ c : F, ∀ x : V, z.val x = c • x := by
  obtain ⟨c, hce⟩ := root_centralizer_preserves_line Q e f he hf hef hQ a b ha hab z
    (fun g hg => hz g (rootSubgroup_le_elementary Q e he hg))
  let a' : complement Q f e := ⟨a.val, a.prop.2, a.prop.1⟩
  let b' : complement Q f e := ⟨b.val, b.prop.2, b.prop.1⟩
  have hfe : Q.polarBilin f e = 1 := (polar_swap Q f e).trans hef
  obtain ⟨d, hdf⟩ := root_centralizer_preserves_line Q f e hf he hfe hQ a' b' ha hab z
    (fun g hg => hz g (rootSubgroup_le_elementary Q f hf hg))
  have hda := centralizer_isotropic_parameter Q z hz e f he hef a ha d hdf
  have hca := centralizer_isotropic_parameter Q z hz f e hf hfe a' ha c hce
  change z.val a.val = c • a.val at hca
  have hcd : c = d := by
    have h := congrArg (fun y => Q.polarBilin y b.val) (hca.symm.trans hda)
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hab, mul_one] using h
  subst d
  have hw (w : complement Q e f) : z.val w.val = c • w.val := by
    have hew : Q.polarBilin e w.val = 0 := (polar_swap Q e w.val).trans w.prop.1
    have hfw : Q.polarBilin f w.val = 0 := (polar_swap Q f w.val).trans w.prop.2
    have hv : siegel Q e w.val f = f - w.val - Q w.val • e := by
      simp only [siegel, hfw, hfe, zero_smul, add_zero, one_smul, mul_one]
    have h := centralizer_siegel_commutes Q z hz e w.val he hew f
    rw [hv, map_sub, map_sub, map_smul, hdf, hce, map_smul] at h
    change c • f - z.val w.val - Q w.val • (c • e) = c • siegel Q e w.val f at h
    rw [hv, smul_sub, smul_sub, smul_comm c (Q w.val) e] at h
    exact sub_right_inj.mp (sub_left_inj.mp h)
  refine ⟨c, ?_⟩
  intro x
  let s := split Q e f he hf hef
  have hx := s.symm_apply_apply x
  change (s x).1.1 • e + (s x).1.2 • f + (s x).2.val = x at hx
  rw [← hx, map_add, map_add, map_smul, map_smul, hce, hdf, hw,
    smul_add, smul_add, smul_comm c (s x).1.1 e, smul_comm c (s x).1.2 f]
end Atlas.Orthogonal
