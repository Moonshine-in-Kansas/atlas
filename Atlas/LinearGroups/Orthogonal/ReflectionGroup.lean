import Atlas.LinearGroups.Orthogonal.DeterminantSign
import Atlas.LinearAlgebra.QuadraticEqualValue
import Atlas.LinearAlgebra.QuadraticLineExtension

/-! # Actual reflection subgroups and transport through a nondegenerate line -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def reflectionSubgroup : Subgroup (isometrySubgroup Q) :=
  Subgroup.closure {g | ∃ a ha, g = reflectionElement Q a ha}

theorem reflectionElement_mem (a : V) (ha : Q a ≠ 0) :
    reflectionElement Q a ha ∈ reflectionSubgroup Q := Subgroup.subset_closure ⟨a, ha, rfl⟩

theorem reflectionSubgroup_transport (h2 : (2 : F) ≠ 0) (u v : V)
    (hu : Q u ≠ 0) (hval : Q u = Q v) :
    ∃ g : isometrySubgroup Q, g ∈ reflectionSubgroup Q ∧ g.val u = v := by
  by_cases hsub : Q (u-v) = 0
  · have hsum : Q (u+v) ≠ 0 := by
      have hs := sub_value Q u v
      have ha := QuadraticMap.map_add Q u v
      change Q (u+v) = Q u + Q v + Q.polarBilin u v at ha
      have he : Q (u+v) = (2 : F)^2 * Q u := by rw [hval] at hs ha ⊢; linear_combination ha + hs - hsub
      rw [he]
      exact mul_ne_zero (pow_ne_zero _ h2) hu
    have hd : Q (u-(-v)) ≠ 0 := by simpa only [sub_neg_eq_add] using hsum
    let r := reflectionElement Q (u-(-v)) hd
    let s := reflectionElement Q v (hval ▸ hu)
    refine ⟨s*r, (reflectionSubgroup Q).mul_mem (reflectionElement_mem _ _ _) (reflectionElement_mem _ _ _), ?_⟩
    change s.val (r.val u) = v
    have hr : r.val u = -v := reflection_equal_value Q u (-v) (by rwa [Q.map_neg]) hd
    rw [hr, map_neg]
    change -(reflectionLinear Q v (hval ▸ hu) v) = v
    rw [reflection_self, neg_neg]
  · exact ⟨reflectionElement Q (u-v) hsub, reflectionElement_mem _ _ _, reflection_equal_value Q u v hval hsub⟩

variable (a : V) (ha : Q.polarBilin a a ≠ 0)

def lineExtensionHom : isometrySubgroup (linePerpForm Q a) →* isometrySubgroup Q where
  toFun g := (isometryCarrierEquiv Q).symm (lineExtension Q a ha (isometryCarrierEquiv _ g))
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun (linear_ext_linePerp Q a ha _ _
      (lineExtension_fix Q a ha _) (fun w => lineExtension_apply Q a ha _ w)) x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply LinearMap.congr_fun (linear_ext_linePerp Q a ha _ _ ?_ ?_) x
    · change lineExtension Q a ha (isometryCarrierEquiv _ (g*h)) a =
        lineExtension Q a ha (isometryCarrierEquiv _ g) (lineExtension Q a ha (isometryCarrierEquiv _ h) a)
      rw [lineExtension_fix, lineExtension_fix, lineExtension_fix]
    · intro w
      change lineExtension Q a ha (isometryCarrierEquiv _ (g*h)) w.val =
        lineExtension Q a ha (isometryCarrierEquiv _ g) (lineExtension Q a ha (isometryCarrierEquiv _ h) w.val)
      rw [lineExtension_apply, lineExtension_apply, lineExtension_apply]
      rfl

theorem lineExtensionHom_reflection (u : linePerp Q a) (hu : (linePerpForm Q a) u ≠ 0) :
    lineExtensionHom Q a ha (reflectionElement (linePerpForm Q a) u hu) = reflectionElement Q u.val hu := by
  change (isometryCarrierEquiv Q).symm (lineExtension Q a ha (reflectionIsometry (linePerpForm Q a) u hu)) = _
  rw [lineExtension_reflection Q a ha u hu]
  rfl

theorem lineExtensionHom_mem (k : isometrySubgroup (linePerpForm Q a))
    (hk : k ∈ reflectionSubgroup (linePerpForm Q a)) :
    lineExtensionHom Q a ha k ∈ reflectionSubgroup Q := by
  have hl : reflectionSubgroup (linePerpForm Q a) ≤ (reflectionSubgroup Q).comap (lineExtensionHom Q a ha) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨u, hu, rfl⟩
    change lineExtensionHom Q a ha (reflectionElement (linePerpForm Q a) u hu) ∈ reflectionSubgroup Q
    rw [lineExtensionHom_reflection]
    exact reflectionElement_mem Q u.val hu
  exact hl hk

end Atlas.Orthogonal
