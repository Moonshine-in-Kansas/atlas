import Atlas.LinearGroups.SuzukiFamily.RootSubgroup
import Atlas.LinearGroups.SuzukiFamily.RootSolvable

/-! A reusable structural comparison for the two conventions of the Suzuki
root-group cocycle. Every use requires an actual bijective parameterization
and its multiplication law; this module does not assume an ambient Ree root
group exists or assert membership of any unverified operator. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The involutive shear interchanges theta(a)*c and a*theta(c) conventions. -/
def suzukiParameterShear (m : ℕ) : (F × F) ≃ (F × F) where
  toFun p := (p.1, p.2 + p.1 * Atlas.SuzukiFamily.theta F m p.1)
  invFun p := (p.1, p.2 + p.1 * Atlas.SuzukiFamily.theta F m p.1)
  left_inv p := by
    apply Prod.ext
    · rfl
    · simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  right_inv p := by
    apply Prod.ext
    · rfl
    · simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem suzukiParameterShear_cocycle (m : ℕ) (a u b v : F) :
    (u + v + Atlas.SuzukiFamily.theta F m a * b) +
      (a + b) * Atlas.SuzukiFamily.theta F m (a + b) =
    (u + a * Atlas.SuzukiFamily.theta F m a) +
      (v + b * Atlas.SuzukiFamily.theta F m b) +
      a * Atlas.SuzukiFamily.theta F m b := by
  rw [map_add]
  calc
    _ = ((u + a * Atlas.SuzukiFamily.theta F m a) +
        (v + b * Atlas.SuzukiFamily.theta F m b) +
        a * Atlas.SuzukiFamily.theta F m b) +
        (Atlas.SuzukiFamily.theta F m a * b + Atlas.SuzukiFamily.theta F m a * b) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

variable {H : Type*} [Group H]

/-- Set-level comparison from a concrete bijective parameterization. -/
def rootSuzukiParameterEquiv (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (U : F → F → H) (hbij : Function.Bijective (fun p : F × F => U p.1 p.2)) :
    H ≃ Atlas.SuzukiFamily.rootSubgroup m hcard :=
  (Equiv.ofBijective (fun p : F × F => U p.1 p.2) hbij).symm.trans
    ((suzukiParameterShear (F := F) m).trans (Atlas.SuzukiFamily.rootParameters m hcard))

theorem rootSuzukiParameterEquiv_apply (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (U : F → F → H) (hbij : Function.Bijective (fun p : F × F => U p.1 p.2))
    (a b : F) :
    rootSuzukiParameterEquiv m hcard U hbij (U a b) =
      Atlas.SuzukiFamily.rootParameters m hcard
        (a, b + a * Atlas.SuzukiFamily.theta F m a) := by
  let e := Equiv.ofBijective (fun p : F × F => U p.1 p.2) hbij
  have he : e.symm (U a b) = (a,b) := e.symm_apply_apply (a,b)
  change Atlas.SuzukiFamily.rootParameters m hcard
    (suzukiParameterShear m (e.symm (U a b))) = _
  rw [he]
  rfl

/-- A concrete root-group law supplies an isomorphism to the retained actual
Suzuki matrix root subgroup. No target-order recognition is involved. -/
def rootSuzukiEquivOfParameters (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (U : F → F → H) (hbij : Function.Bijective (fun p : F × F => U p.1 p.2))
    (hmul : ∀ a b c d : F,
      U a b * U c d = U (a+c) (b+d+Atlas.SuzukiFamily.theta F m a*c)) :
    H ≃* Atlas.SuzukiFamily.rootSubgroup m hcard where
  toEquiv := rootSuzukiParameterEquiv m hcard U hbij
  map_mul' x y := by
    obtain ⟨⟨a,b⟩, rfl⟩ := hbij.surjective x
    obtain ⟨⟨c,d⟩, rfl⟩ := hbij.surjective y
    change rootSuzukiParameterEquiv m hcard U hbij (U a b * U c d) =
      rootSuzukiParameterEquiv m hcard U hbij (U a b) *
        rootSuzukiParameterEquiv m hcard U hbij (U c d)
    rw [hmul, rootSuzukiParameterEquiv_apply, rootSuzukiParameterEquiv_apply,
      rootSuzukiParameterEquiv_apply]
    apply Subtype.ext
    change Atlas.SuzukiFamily.rootElement m (a+c)
      ((b+d+Atlas.SuzukiFamily.theta F m a*c) +
        (a+c)*Atlas.SuzukiFamily.theta F m (a+c)) =
      Atlas.SuzukiFamily.rootElement m a (b+a*Atlas.SuzukiFamily.theta F m a) *
        Atlas.SuzukiFamily.rootElement m c (d+c*Atlas.SuzukiFamily.theta F m c)
    rw [Atlas.SuzukiFamily.rootElement_mul m hcard,
      suzukiParameterShear_cocycle]

/-- Conditional reuse of the already verified root-subgroup order. -/
theorem card_of_rootSuzuki_parameters (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (U : F → F → H) (hbij : Function.Bijective (fun p : F × F => U p.1 p.2))
    (hmul : ∀ a b c d : F,
      U a b * U c d = U (a+c) (b+d+Atlas.SuzukiFamily.theta F m a*c)) :
    Nat.card H = (Nat.card F)^2 := by
  rw [Nat.card_congr (rootSuzukiEquivOfParameters m hcard U hbij hmul).toEquiv]
  exact Atlas.SuzukiFamily.card_rootSubgroup m hcard

/-- Conditional reuse of the verified additive-by-additive solvability proof. -/
theorem solvable_of_rootSuzuki_parameters (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (U : F → F → H) (hbij : Function.Bijective (fun p : F × F => U p.1 p.2))
    (hmul : ∀ a b c d : F,
      U a b * U c d = U (a+c) (b+d+Atlas.SuzukiFamily.theta F m a*c)) :
    Group.IsSolvable H := by
  letI := Atlas.SuzukiFamily.rootSubgroup_solvable m hcard
  exact Group.isSolvable_of_isSolvable_injective
    (f := (rootSuzukiEquivOfParameters m hcard U hbij hmul).toMonoidHom)
    (rootSuzukiEquivOfParameters m hcard U hbij hmul).injective

end Atlas.ReeF4
