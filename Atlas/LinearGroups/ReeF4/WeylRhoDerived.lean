import Atlas.LinearGroups.ReeF4.RootSuzukiLeviGenerators
import Atlas.LinearGroups.ReeF4.RootGroupDerived
import Atlas.LinearGroups.ReeF4.WeylModel
import Atlas.LinearGroups.SuzukiFamily.Perfect

/-! The actual short-root Weyl generator lies in the derived intrinsic model.
Only SuzukiFamily.weyl_root_word is reused from its Perfect module. That word
is proved from the concrete Bruhat rewrite and does not use Suzuki perfectness
or simplicity. This module makes no ambient perfectness assertion. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The concrete Suzuki Weyl word after applying the actual full-space Levi map. -/
theorem weylRho_root_word {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    (shortRootPairEquiv m hcard 1 0)⁻¹ *
      (weylRho * shortRootPairEquiv m hcard 0 1 * weylRho) *
      (shortRootPairEquiv m hcard 1 1)⁻¹ = weylRho := by
  have h10 : suzukiLeviHom (SuzukiFamily.rootElement m (1:F) 1) =
      shortRootPairEquiv m hcard 1 0 := by
    simpa only [map_one,one_mul,zero_add] using suzukiLeviHom_root m hcard 1 0
  have h01 : suzukiLeviHom (SuzukiFamily.rootElement m (0:F) 1) =
      shortRootPairEquiv m hcard 0 1 := by
    simpa only [zero_mul,add_zero] using suzukiLeviHom_root m hcard 0 1
  have h11 : suzukiLeviHom (SuzukiFamily.rootElement m (1:F) 0) =
      shortRootPairEquiv m hcard 1 1 := by
    simpa only [map_one,one_mul,CharTwo.add_self_eq_zero] using
      suzukiLeviHom_root m hcard 1 1
  have h := congrArg suzukiLeviHom (SuzukiFamily.weyl_root_word m hcard)
  simpa only [map_mul,map_inv,suzukiLeviHom_weyl,h10,h01,h11] using h

def weylRhoModel (m : ℕ) : Model F m :=
  ⟨weylRho,weylOperator_mem_modelSubgroup m 0⟩

private theorem weylRhoModel_val (m : ℕ) :
    (weylRhoModel (F := F) m).val = weylRho := rfl

private theorem rootModel_val {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a b : F) :
    (shortRootModelEmbedding hcard (shortRootParameters m hcard (a,b))).val =
      shortRootPairEquiv m hcard a b := rfl

theorem weylRhoModel_inv (m : ℕ) : (weylRhoModel (F := F) m)⁻¹ = weylRhoModel m := by
  apply Subtype.ext
  simp only [Subgroup.coe_inv,weylRhoModel_val]
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using weylRho_square (F := F)

theorem weylRhoModel_root_word {m : ℕ} (hcard : Nat.card F = 2^(2*m+1)) :
    (shortRootModelEmbedding hcard (shortRootParameters m hcard (1,0)))⁻¹ *
      (weylRhoModel m * shortRootModelEmbedding hcard (shortRootParameters m hcard (0,1)) *
        weylRhoModel m) *
      (shortRootModelEmbedding hcard (shortRootParameters m hcard (1,1)))⁻¹ =
      weylRhoModel m := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,rootModel_val,weylRhoModel_val]
  exact weylRho_root_word hcard

theorem weylRhoModel_mem_commutator {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (hm : 1 ≤ m) :
    weylRhoModel (F := F) m ∈ commutator (Model F m) := by
  have h10 := shortRootModelParameter_mem_commutator hcard hm (1:F) 0
  have h01 := shortRootModelParameter_mem_commutator hcard hm (0:F) 1
  have h11 := shortRootModelParameter_mem_commutator hcard hm (1:F) 1
  have hc := (inferInstance : (commutator (Model F m)).Normal).conj_mem _ h01 (weylRhoModel m)
  rw [weylRhoModel_inv] at hc
  rw [←weylRhoModel_root_word hcard]
  exact (commutator (Model F m)).mul_mem
    ((commutator (Model F m)).mul_mem ((commutator (Model F m)).inv_mem h10) hc)
    ((commutator (Model F m)).inv_mem h11)

end Atlas.ReeF4
