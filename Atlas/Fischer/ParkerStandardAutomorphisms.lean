import Atlas.Fischer.ParkerLoopLifts
import Atlas.Fischer.ParkerCodeAction

namespace Atlas.Fischer
open Atlas.Codes

/-- Actual loop automorphisms fixing signs and inducing marked code permutations. -/
def IsParkerStandardAutomorphism (e : Equiv.Perm ParkerLoop) : Prop :=
  (∀ x y, e (parkerLoopMultiply x y) = parkerLoopMultiply (e x) (e y)) ∧
  (∀ s : Bit, e (0, s) = (0, s)) ∧
  ∃ g : Mathieu24CodeModel, ∀ x, (e x).1 = parkerCodeEquiv g x.1

def parkerStandardAutomorphisms : Subgroup (Equiv.Perm ParkerLoop) where
  carrier := IsParkerStandardAutomorphism
  one_mem' := by
    refine ⟨fun _ _ => rfl, fun _ => rfl, 1, ?_⟩
    intro x
    exact (parkerCodeEquiv_one x.1).symm
  mul_mem' := by
    rintro e f ⟨he, hse, g, hge⟩ ⟨hf, hsf, h, hhf⟩
    refine ⟨?_, ?_, g * h, ?_⟩
    · intro x y
      change e (f (parkerLoopMultiply x y)) = _
      rw [hf, he]
      rfl
    · intro s
      change e (f (0, s)) = _
      rw [hsf, hse]
    · intro x
      change (e (f x)).1 = _
      rw [hge, hhf, parkerCodeEquiv_mul]
  inv_mem' := by
    rintro e ⟨he, hs, g, hg⟩
    refine ⟨?_, ?_, g⁻¹, ?_⟩
    · intro x y
      apply e.injective
      change e (e.symm (parkerLoopMultiply x y)) =
        e (parkerLoopMultiply (e.symm x) (e.symm y))
      rw [e.apply_symm_apply, he, e.apply_symm_apply, e.apply_symm_apply]
    · intro s
      apply e.injective
      change e (e.symm (0, s)) = e (0, s)
      rw [e.apply_symm_apply, hs]
    · intro x
      have hh := hg (e.symm x)
      rw [e.apply_symm_apply] at hh
      have hi := congrArg (parkerCodeEquiv g⁻¹) hh
      rw [← parkerCodeEquiv_mul, inv_mul_cancel, parkerCodeEquiv_one] at hi
      exact hi.symm

abbrev ParkerStandardGroup := parkerStandardAutomorphisms

noncomputable def parkerStandardInduced (e : ParkerStandardGroup) : Mathieu24CodeModel :=
  Classical.choose e.property.2.2

theorem parkerStandardInduced_spec (e : ParkerStandardGroup) (x : ParkerLoop) :
    (e.val x).1 = parkerCodeEquiv (parkerStandardInduced e) x.1 :=
  Classical.choose_spec e.property.2.2 x

noncomputable def parkerStandardProjection : ParkerStandardGroup →* Mathieu24CodeModel where
  toFun := parkerStandardInduced
  map_one' := by
    apply parkerCodeEquiv_faithful
    intro a
    exact (parkerStandardInduced_spec 1 (a, 0)).symm
  map_mul' e f := by
    apply parkerCodeEquiv_faithful
    intro a
    calc
      parkerCodeEquiv (parkerStandardInduced (e * f)) a =
          ((e * f).val (a, 0)).1 := (parkerStandardInduced_spec (e * f) (a, 0)).symm
      _ = parkerCodeEquiv (parkerStandardInduced e) (f.val (a, 0)).1 :=
        parkerStandardInduced_spec e (f.val (a, 0))
      _ = parkerCodeEquiv (parkerStandardInduced e)
          (parkerCodeEquiv (parkerStandardInduced f) a) := by
        rw [parkerStandardInduced_spec f (a, 0)]
      _ = parkerCodeEquiv (parkerStandardInduced e * parkerStandardInduced f) a :=
        (parkerCodeEquiv_mul _ _ a).symm

theorem parkerStandardProjection_spec (e : ParkerStandardGroup) (x : ParkerLoop) :
    (e.val x).1 = parkerCodeEquiv (parkerStandardProjection e) x.1 :=
  parkerStandardInduced_spec e x

theorem parkerStandardGroup_finite : Finite ParkerStandardGroup := inferInstance

end Atlas.Fischer
