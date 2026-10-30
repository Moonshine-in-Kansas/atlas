import Mathlib.Tactic.Group

namespace Atlas.GroupTheory
variable {G : Type*} [Group G]

/-- Moving the seven Weyl letters right isolates precisely seven conjugated
root elements; this is an abstract group identity, not a matrix computation. -/
theorem sevenPivotFactorization (r s l0 l1 l2 l3 x0 x1 x2 : G)
    (hr : r⁻¹=r) (hs : s⁻¹=s) :
    (s*l0)⁻¹ * ((r*x0)⁻¹ * ((s*l1)⁻¹ * ((r*x1)⁻¹ *
      ((s*l2)⁻¹ * ((r*x2)⁻¹ * (s*l3)⁻¹))))) =
    l0⁻¹ * ((s*x0⁻¹*s⁻¹) *
    (((s*r)*l1⁻¹*(s*r)⁻¹) *
    (((s*r*s)*x1⁻¹*(s*r*s)⁻¹) *
    (((s*r)^2*l2⁻¹*((s*r)^2)⁻¹) *
    ((((s*r)^2*s)*x2⁻¹*((s*r)^2*s)⁻¹) *
    (((s*r)^3*l3⁻¹*((s*r)^3)⁻¹) * ((s*r)^3*s))))))) := by
  simp only [pow_succ,pow_zero,mul_one]
  group
  simp only [zpow_neg_one,hr,hs]


 theorem sevenPivotFactorizationInverse (r s l0 l1 l2 l3 x0 x1 x2 : G)
    (hr : r⁻¹=r) (hs : s⁻¹=s) :
    (s*l0)⁻¹ * ((r*x0)⁻¹ * ((s*l1)⁻¹ * ((r*x1)⁻¹ *
      ((s*l2)⁻¹ * ((r*x2)⁻¹ * (s*l3)⁻¹))))) =
    l0⁻¹ * ((s*x0*s⁻¹)⁻¹ *
    (((s*r)*l1*(s*r)⁻¹)⁻¹ *
    (((s*r*s)*x1*(s*r*s)⁻¹)⁻¹ *
    (((s*r)^2*l2*((s*r)^2)⁻¹)⁻¹ *
    ((((s*r)^2*s)*x2*((s*r)^2*s)⁻¹)⁻¹ *
    (((s*r)^3*l3*((s*r)^3)⁻¹)⁻¹ * ((s*r)^3*s))))))) := by
  simp only [pow_succ,pow_zero,mul_one]
  group
  simp only [zpow_neg_one,hr,hs]
end Atlas.GroupTheory
