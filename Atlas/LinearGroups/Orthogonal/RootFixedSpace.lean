import Atlas.LinearGroups.Orthogonal.RootSubgroupCoordinates
import Atlas.LinearAlgebra.QuadraticSplit

/-! # The fixed space of a singular-line root subgroup -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V) (he : Q e = 0) (hf : Q f = 0)
  (hef : Q.polarBilin e f = 1)

theorem rootSubgroup_fixes_direction (g : isometrySubgroup Q) (hg : g ∈ rootSubgroup Q e he) :
    g.val e = e := by
  obtain ⟨v, rfl⟩ := hg
  exact siegel_fix Q e v.toAdd.val he v.toAdd.prop

include hf hef in
/-- A perpendicular hyperbolic pair makes the common fixed space exactly the root line. -/
theorem root_fixed_iff (hQ : Q.polarBilin.Nondegenerate)
    (a b : complement Q e f) (ha : Q a.val = 0) (hab : Q.polarBilin a.val b.val = 1)
    (x : V) :
    (∀ g ∈ rootSubgroup Q e he, g.val x = x) ↔ ∃ c : F, x = c • e := by
  constructor
  · intro hfix
    have hr (w : complement Q e f) : siegel Q e w.val x = x := by
      apply hfix (rootComplementHom Q e f he (Multiplicative.ofAdd w))
      rw [← rootComplementHom_range Q e f he hef]
      exact ⟨Multiplicative.ofAdd w, rfl⟩
    have hxe : Q.polarBilin x e = 0 := by
      have h := congrArg (fun y => Q.polarBilin y b.val) (hr a)
      have heb : Q.polarBilin e b.val = 0 := (polar_swap Q e b.val).trans b.prop.1
      simp only [siegel, ha, zero_mul, zero_smul, sub_zero, map_sub, map_add,
        map_smul, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, heb, hab, mul_zero, mul_one, add_zero] at h
      exact sub_eq_self.mp h
    have hxw (w : complement Q e f) : Q.polarBilin x w.val = 0 := by
      have h := congrArg (fun y => Q.polarBilin y f) (hr w)
      simp only [siegel, hxe, mul_zero, zero_smul, sub_zero, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hef, mul_one] at h
      exact add_eq_left.mp h
    have hee : Q.polarBilin e e = 0 := by rw [polar_self, he, mul_zero]
    let d := x - Q.polarBilin x f • e
    have hde : Q.polarBilin d e = 0 := by
      simp only [d, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hxe, hee, mul_zero, sub_self]
    have hdf : Q.polarBilin d f = 0 := by
      simp only [d, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hef, mul_one, sub_self]
    have hdw (w : complement Q e f) : Q.polarBilin d w.val = 0 := by
      have hew : Q.polarBilin e w.val = 0 := (polar_swap Q e w.val).trans w.prop.1
      simp only [d, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul, hxw, hew, mul_zero, sub_self]
    have hd : d = 0 := by
      apply hQ.1
      intro y
      let s := split Q e f he hf hef
      have hy := s.symm_apply_apply y
      change (s y).1.1 • e + (s y).1.2 • f + (s y).2.val = y at hy
      rw [← hy, map_add, map_add, map_smul, map_smul, hde, hdf, hdw,
        smul_zero, smul_zero, add_zero, add_zero]
    exact ⟨Q.polarBilin x f, sub_eq_zero.mp hd⟩
  · rintro ⟨c, rfl⟩ g hg
    rw [map_smul, rootSubgroup_fixes_direction Q e he g hg]

include hf hef in
/-- Any full isometry centralizing this root subgroup preserves its singular direction. -/
theorem root_centralizer_preserves_line (hQ : Q.polarBilin.Nondegenerate)
    (a b : complement Q e f) (ha : Q a.val = 0) (hab : Q.polarBilin a.val b.val = 1)
    (z : isometrySubgroup Q)
    (hz : ∀ g ∈ rootSubgroup Q e he, g*z = z*g) :
    ∃ c : F, z.val e = c • e := by
  apply (root_fixed_iff Q e f he hf hef hQ a b ha hab (z.val e)).mp
  intro g hg
  have h := congrArg (fun k : isometrySubgroup Q => k.val e) (hz g hg)
  change g.val (z.val e) = z.val (g.val e) at h
  rw [rootSubgroup_fixes_direction Q e he g hg] at h
  exact h
end Atlas.Orthogonal
