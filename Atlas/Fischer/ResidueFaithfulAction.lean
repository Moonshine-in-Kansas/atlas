import Atlas.Fischer.ResidueActionKernel
import Atlas.Fischer.ResidueOrder

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The central quotient acts on the original residue distinguished point set.
No identification of quotient images is assumed. -/
def residueQuotientAction (S : Finset Omega) : ResidueGroup S →* Equiv.Perm (ResiduePoint S) :=
  QuotientGroup.lift (residueCentralElementary S) (residueConjugationHom S)
    (residueElementary_le_action_kernel S)

theorem residueQuotientAction_injective (S : Finset Omega) (hS : S.card ≤ 2) :
    Function.Injective (residueQuotientAction S) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (residueConjugationHom_kernel S hS).symm

instance residueGroupMulAction (S : Finset Omega) : MulAction (ResidueGroup S) (ResiduePoint S) where
  smul g x := residueQuotientAction S g x
  one_smul x := by
    change residueQuotientAction S 1 x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    change residueQuotientAction S (g*h) x = residueQuotientAction S g (residueQuotientAction S h x)
    rw [map_mul]
    rfl

theorem residueGroup_faithful (S : Finset Omega) (hS : S.card ≤ 2) :
    FaithfulSMul (ResidueGroup S) (ResiduePoint S) where
  eq_of_smul_eq_smul h := residueQuotientAction_injective S hS (Equiv.ext h)

instance residueGroup_faithful_of_small (S : Finset Omega) [Fact (S.card ≤ 2)] :
    FaithfulSMul (ResidueGroup S) (ResiduePoint S) := residueGroup_faithful S Fact.out

@[simp] theorem residueQuotientAction_mk (S : Finset Omega) (g : residueCentralizer S) :
    residueQuotientAction S (QuotientGroup.mk g) = residueConjugationHom S g := rfl

theorem residueGroup_mk_smul_val (S : Finset Omega) (g : residueCentralizer S) (x : ResiduePoint S) :
    ((QuotientGroup.mk g : ResidueGroup S) • x).val = g.val*x.val*g.val⁻¹ := rfl

end Atlas.Fischer
