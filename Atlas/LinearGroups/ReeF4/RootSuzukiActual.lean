import Atlas.LinearGroups.ReeF4.RootSuzukiComparison
import Atlas.LinearGroups.ReeF4.RootGroupSubgroup

/-! The concrete two-parameter subgroup of the actual 26-dimensional linear
automorphisms is isomorphic to the retained Suzuki matrix root subgroup.
Membership in the full Ree candidate is a separate structural obligation. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem shortRootParameters_mul (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b c d : F) :
    shortRootParameters m hcard (a,b) * shortRootParameters m hcard (c,d) =
      shortRootParameters m hcard (a+c,b+d+Atlas.SuzukiFamily.theta F m a*c) := by
  apply Subtype.ext
  exact shortRootPairEquiv_mul m hcard a b c d

/-- Explicit parameter-shear comparison of two actual root-group models. -/
def shortRootSuzukiEquiv (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    shortRootSubgroup m hcard ≃* Atlas.SuzukiFamily.rootSubgroup m hcard :=
  rootSuzukiEquivOfParameters m hcard
    (fun a b => shortRootParameters m hcard (a,b))
    (shortRootParameters m hcard).bijective
    (shortRootParameters_mul m hcard)

theorem shortRootSuzukiEquiv_parameters (m : ℕ) (hcard : Nat.card F = 2^(2*m+1))
    (a b : F) :
    shortRootSuzukiEquiv m hcard (shortRootParameters m hcard (a,b)) =
      Atlas.SuzukiFamily.rootParameters m hcard
        (a,b+a*Atlas.SuzukiFamily.theta F m a) :=
  rootSuzukiParameterEquiv_apply m hcard
    (fun a b => shortRootParameters m hcard (a,b))
    (shortRootParameters m hcard).bijective a b

/-- Solvability transferred through the explicit concrete comparison. -/
theorem shortRootSubgroup_solvable (m : ℕ) (hcard : Nat.card F = 2^(2*m+1)) :
    Group.IsSolvable (shortRootSubgroup m hcard) :=
  solvable_of_rootSuzuki_parameters m hcard
    (fun a b => shortRootParameters m hcard (a,b))
    (shortRootParameters m hcard).bijective
    (shortRootParameters_mul m hcard)

end Atlas.ReeF4
