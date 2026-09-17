import Atlas.Fischer.ReflectingRootQuadraticBound
import Atlas.Fischer.ReflectingRootRays

noncomputable section
namespace Atlas.Fischer

/-- An extremal finite family exhausts all intrinsic reflecting rays. The proof
adjoins one hypothetical missing ray and applies the absolute bound, without
assuming that the full intrinsic set is finite. -/
theorem extremalReflectingRays_exhaust {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hi : Function.Injective (fun j => rootRay (r j)))
    (hc : Fintype.card J = 306936) (x : Coordinates) (hx : IsReflectingRoot x) :
    ∃ j, rootRay x = rootRay (r j) := by
  classical
  by_contra h
  have hn : ∀ j, rootRay x ≠ rootRay (r j) := by simpa only [not_exists] using h
  let v : Option J → Coordinates := fun j => j.elim x r
  have hv : ∀ j, IsReflectingRoot (v j) := by
    intro j
    cases j with
    | none => exact hx
    | some j => exact hr j
  have hinj : Function.Injective (fun j => rootRay (v j)) := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim (hn j he)
    | some i =>
      cases j with
      | none => exact False.elim (hn i he.symm)
      | some j => exact congrArg Option.some (hi he)
  have hb := reflectingRoot_finite_family_bound v hv (fun i j hij he =>
    hij (hinj ((rootRay_eq_iff_mu3 (v i) (v j)).mpr he).symm))
  rw [Fintype.card_option, hc] at hb
  omega

theorem extremalReflectingRays_phase {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hi : Function.Injective (fun j => rootRay (r j)))
    (hc : Fintype.card J = 306936) (x : Coordinates) (hx : IsReflectingRoot x) :
    ∃ j, ∃ a : Mu3, x = (a.val.val : Scalar) • r j := by
  obtain ⟨j, hj⟩ := extremalReflectingRays_exhaust r hr hi hc x hx
  exact ⟨j, (rootRay_eq_iff_mu3 (r j) x).mp hj⟩

/-- Equality with the intrinsic reflecting-root predicate, conditional only on
an actual finite extremal family and its verified ray injection. -/
theorem extremalReflectingRays_membership {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hi : Function.Injective (fun j => rootRay (r j)))
    (hc : Fintype.card J = 306936) (x : Coordinates) :
    IsReflectingRoot x ↔ ∃ j, x ∈ rootRay (r j) := by
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := extremalReflectingRays_exhaust r hr hi hc x hx
    exact ⟨j, hj ▸ root_mem_rootRay x⟩
  · rintro ⟨j, hj⟩
    exact rootRay_members_are_reflecting _ (hr j) hj

theorem extremalReflectingRays_set_eq {J : Type*} [Fintype J]
    (r : J → Coordinates) (hr : ∀ j, IsReflectingRoot (r j))
    (hi : Function.Injective (fun j => rootRay (r j)))
    (hc : Fintype.card J = 306936) :
    {x : Coordinates | IsReflectingRoot x} = ⋃ j, (rootRay (r j) : Set Coordinates) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe]
  exact extremalReflectingRays_membership r hr hi hc x

end Atlas.Fischer
