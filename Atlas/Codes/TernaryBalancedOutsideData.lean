import Atlas.Codes.TernaryBalancedAction
import Atlas.Codes.TernaryCoordinateBasis

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
namespace Atlas.Codes

def ternaryBalancedOutsidePermutation (a : Fin 6) : Equiv.Perm (Fin 12) where
  toFun := (![![0,1,2,3,4,5,6,7,8,9,10,11],
    ![0,1,2,4,5,3,8,9,11,10,7,6],
    ![0,1,2,5,3,4,11,10,6,7,9,8],
    ![0,1,2,6,11,8,3,10,5,9,7,4],
    ![0,1,2,8,6,11,4,7,3,10,9,5],
    ![0,1,2,11,8,6,5,9,4,7,10,3]]) a
  invFun := (![![0,1,2,3,4,5,6,7,8,9,10,11],
    ![0,1,2,5,3,4,11,10,6,7,9,8],
    ![0,1,2,4,5,3,8,9,11,10,7,6],
    ![0,1,2,6,11,8,3,10,5,9,7,4],
    ![0,1,2,8,6,11,4,7,3,10,9,5],
    ![0,1,2,11,8,6,5,9,4,7,10,3]]) a
  left_inv := by revert a; decide +kernel
  right_inv := by revert a; decide +kernel

theorem ternaryBalancedOutsidePermutation_check : ∀ a : Fin 6, ∀ j : Fin 6,
    (fun i => ternaryEncoder (Pi.single j 1) ((ternaryBalancedOutsidePermutation a).symm i)) =
      ternaryEncoder (ternaryDecoder (fun i => ternaryEncoder (Pi.single j 1) ((ternaryBalancedOutsidePermutation a).symm i))) := by
  decide +kernel

theorem ternaryBalancedOutsidePermutation_mem (a : Fin 6) :
    ternaryBalancedOutsidePermutation a ∈ ternaryPureAutomorphism := by
  apply ternaryCoordinatePreserves_of_basis
  intro j
  rw [ternaryBalancedOutsidePermutation_check]
  exact ⟨_,rfl⟩

def ternaryBalancedOutsideAutomorphism (a : Fin 6) : TernaryPureAutomorphism :=
  ⟨ternaryBalancedOutsidePermutation a,ternaryBalancedOutsidePermutation_mem a⟩

theorem ternaryBalancedOutsidePermutation_fixed : ∀ a : Fin 6,
    (fun i => ternaryBalancedBase ((ternaryBalancedOutsidePermutation a).symm i))=ternaryBalancedBase := by
  decide +kernel

theorem ternaryBalancedOutsidePermutation_transitive : ∀ j : Fin 12,
    j ∉ ternarySupport ternaryBalancedBase →
      ∃ a : Fin 6,ternaryBalancedOutsidePermutation a 3=j := by decide +kernel

end Atlas.Codes
