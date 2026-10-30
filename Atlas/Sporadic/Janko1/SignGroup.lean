import Atlas.Sporadic.Janko1.SignCoordinates
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Actual octonion sign automorphisms, parameterized by a binary vector space. -/
namespace Atlas.Janko1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Eight diagonal operators, each tested on the 64 installed octonion basis pairs.
private theorem sign_basis_mul : ∀ a : SignParameters, ∀ i j : Fin 8,
    signLinear a (SplitOctonion.mul (SplitOctonion.basisVector i)
      (SplitOctonion.basisVector j)) =
    SplitOctonion.mul (signLinear a (SplitOctonion.basisVector i))
      (signLinear a (SplitOctonion.basisVector j)) := by decide

theorem signLinear_mul (a : SignParameters) (x y : SplitOctonion.Carrier Field) :
    signLinear a (SplitOctonion.mul x y) =
      SplitOctonion.mul (signLinear a x) (signLinear a y) :=
  SplitOctonion.map_mul_of_basis (signLinear a) (sign_basis_mul a) x y

def signEquiv (a : SignParameters) : SplitOctonion.Carrier Field ≃ₗ[Field]
    SplitOctonion.Carrier Field :=
  LinearEquiv.ofLinearMap (signLinear a) (signLinear a)
    (signLinear_square a) (signLinear_square a)

def signElement (a : SignParameters) : G2.Model Field :=
  ⟨signEquiv a, signLinear_mul a⟩

def signHom : Multiplicative SignParameters →* G2.Model Field where
  toFun a := signElement a.toAdd
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact signLinear_zero
  map_mul' a b := by
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact signLinear_add a.toAdd b.toAdd

theorem signHom_injective : Function.Injective signHom := by
  intro a b h
  have he := congrArg linearRepresentation h
  exact signLinear_injective he

def signSubgroup : Subgroup (G2.Model Field) := signHom.range

noncomputable def signSubgroupEquiv : Multiplicative SignParameters ≃* signSubgroup :=
  MonoidHom.ofInjective signHom_injective

theorem card_signSubgroup : Nat.card signSubgroup = 8 := by
  rw [← Nat.card_congr signSubgroupEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide

theorem signSubgroup_comm (x y : signSubgroup) : x*y = y*x := by
  obtain ⟨a, rfl⟩ := signSubgroupEquiv.surjective x
  obtain ⟨b, rfl⟩ := signSubgroupEquiv.surjective y
  rw [← map_mul, ← map_mul, mul_comm]

theorem signSubgroup_square (x : signSubgroup) : x*x = 1 := by
  obtain ⟨a, rfl⟩ := signSubgroupEquiv.surjective x
  rw [← map_mul]
  have ha : a*a = 1 := by
    change a.toAdd + a.toAdd = 0
    funext i
    exact CharTwo.add_self_eq_zero (a.toAdd i)
  rw [ha, map_one]

end Atlas.Janko1
