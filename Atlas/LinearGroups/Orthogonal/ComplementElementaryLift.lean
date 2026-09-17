import Atlas.LinearGroups.Orthogonal.PairStabilizer
import Atlas.LinearGroups.Orthogonal.Elementary
import Atlas.LinearAlgebra.QuadraticComplementWitness

/-! # The elementary group of a perpendicular complement inside the ambient group -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) (e f : V)
variable (he : Q e = 0) (hf : Q f = 0) (hef : Q.polarBilin e f = 1)

/-- Extend a complement isometry by fixing the displayed hyperbolic pair. -/
def complementLift : isometrySubgroup (complementForm Q e f) →* isometrySubgroup Q :=
  (pairStabilizer Q e f).subtype.comp
    (pairStabilizerEquiv Q e f he hf hef).symm.toMonoidHom

theorem complementLift_fix_e (g : isometrySubgroup (complementForm Q e f)) :
    (complementLift Q e f he hf hef g).val e = e :=
  ((pairStabilizerEquiv Q e f he hf hef).symm g).prop.1

theorem complementLift_fix_f (g : isometrySubgroup (complementForm Q e f)) :
    (complementLift Q e f he hf hef g).val f = f :=
  ((pairStabilizerEquiv Q e f he hf hef).symm g).prop.2

theorem complementLift_apply (g : isometrySubgroup (complementForm Q e f))
    (x : complement Q e f) :
    (complementLift Q e f he hf hef g).val x.val = (g.val x).val := by
  have h := (pairStabilizerEquiv Q e f he hf hef).apply_symm_apply g
  exact congrArg (fun k : isometrySubgroup (complementForm Q e f) => (k.val x).val) h

theorem complementLift_injective : Function.Injective (complementLift Q e f he hf hef) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rw [← complementLift_apply Q e f he hf hef g x,
    ← complementLift_apply Q e f he hf hef h x, hgh]

/-- Extension carries each actual complement Siegel transformation to its ambient formula. -/
theorem complementLift_siegel (u v : complement Q e f)
    (hu : (complementForm Q e f) u = 0)
    (huv : (complementForm Q e f).polarBilin u v = 0) :
    complementLift Q e f he hf hef (siegelElement (complementForm Q e f) u v hu huv) =
      siegelElement Q u.val v.val hu ((complementForm_polar Q e f u v).symm.trans huv) := by
  have he_u : Q.polarBilin e u.val = 0 := (polar_swap Q e u.val).trans u.prop.1
  have he_v : Q.polarBilin e v.val = 0 := (polar_swap Q e v.val).trans v.prop.1
  have hf_u : Q.polarBilin f u.val = 0 := (polar_swap Q f u.val).trans u.prop.2
  have hf_v : Q.polarBilin f v.val = 0 := (polar_swap Q f v.val).trans v.prop.2
  let s := siegelElement Q u.val v.val hu ((complementForm_polar Q e f u v).symm.trans huv)
  have hse : s.val e = e := by
    change siegel Q u.val v.val e = e
    simp [siegel, he_u, he_v]
  have hsf : s.val f = f := by
    change siegel Q u.val v.val f = f
    simp [siegel, hf_u, hf_v]
  let t : pairStabilizer Q e f := ⟨s, hse, hsf⟩
  have ht : pairRestriction Q e f t = siegelElement (complementForm Q e f) u v hu huv := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change siegel Q u.val v.val x.val = (siegel (complementForm Q e f) u v x).val
    simp only [siegel, complementForm_polar]
    rfl
  have hi : (pairStabilizerEquiv Q e f he hf hef).symm
      (siegelElement (complementForm Q e f) u v hu huv) = t := by
    apply (pairStabilizerEquiv Q e f he hf hef).injective
    exact ((pairStabilizerEquiv Q e f he hf hef).apply_symm_apply _).trans ht.symm
  exact congrArg Subtype.val hi

/-- The full complement elementary subgroup embeds in the ambient elementary subgroup. -/
theorem complementLift_maps_elementary :
    (elementarySubgroup (complementForm Q e f)).map (complementLift Q e f he hf hef) ≤
      elementarySubgroup Q := by
  rw [Subgroup.map_le_iff_le_comap]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨u, v, hu, huv, rfl⟩
  change complementLift Q e f he hf hef
    (siegelElement (complementForm Q e f) u v hu huv) ∈ elementarySubgroup Q
  rw [complementLift_siegel Q e f he hf hef]
  exact siegelElement_mem Q _ _ _ _

/-- An elementwise version suitable for geometric orbit arguments. -/
theorem complementLift_mem_elementary (g : isometrySubgroup (complementForm Q e f))
    (hg : g ∈ elementarySubgroup (complementForm Q e f)) :
    complementLift Q e f he hf hef g ∈ elementarySubgroup Q :=
  complementLift_maps_elementary Q e f he hf hef ⟨g, hg, rfl⟩

/-- The actual complement elementary group as a subgroup of the ambient elementary group. -/
def complementElementaryLift : elementarySubgroup (complementForm Q e f) →*
    elementarySubgroup Q where
  toFun g := ⟨complementLift Q e f he hf hef g.val,
    complementLift_mem_elementary Q e f he hf hef g.val g.prop⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

theorem complementElementaryLift_injective :
    Function.Injective (complementElementaryLift Q e f he hf hef) := by
  intro g h hgh
  apply Subtype.ext
  exact complementLift_injective Q e f he hf hef
    (congrArg (fun k : elementarySubgroup Q => k.val) hgh)

end Atlas.Orthogonal

