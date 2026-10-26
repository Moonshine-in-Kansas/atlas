import Atlas.LinearGroups.ReeF4.Weyl
import Atlas.LinearGroups.ReeF4.RootVectors
import Mathlib.GroupTheory.OrderOfElement

/-! Exact order of the actual coordinate rotation, certified by a marked-vector
witness rather than inferred from an abstract dihedral presentation. -/
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [CommRing F] [Nontrivial F]

set_option maxRecDepth 16384 in
theorem weyl_product_pow_four_ne_one :
    ((weylRho (F := F)) * weylSigma) ^ 4 ≠ 1 := by
  intro h
  have hh := congrArg
    (fun e : TraceZero F ≃ₗ[F] TraceZero F =>
      ((e (rootVector (0, 0))) : Carrier F).2 0 0) h
  change (0 : F) = 1 at hh
  exact zero_ne_one hh

theorem weyl_product_order :
    orderOf ((weylRho (F := F)) * weylSigma) = 8 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 2)
    weyl_product_pow_four_ne_one weyl_product_pow_eight

end Atlas.ReeF4
