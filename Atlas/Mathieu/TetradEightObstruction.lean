import Atlas.Mathieu.TetradLocalNormal
import Atlas.GroupTheory.AffineEightObstruction

namespace Atlas.Codes

theorem tetradAffine_no_faithful_eight (i : HexIndex) (X : Type*) [Finite X]
    [MulAction (TetradPointAffine i) X] [FaithfulSMul (TetradPointAffine i) X]
    (hx : Nat.card X = 8) : False := by
  apply Atlas.GroupTheory.affine_no_faithful_eight (hexZeroAffineAction i)
    (show Nat.card (Multiplicative (hexZeroCoordinate i)) = 16 from hexZeroCoordinate_card i) hx
  intro u v hu hv
  obtain ⟨g,hg⟩ := hexPointKernel_nonzero_transitive i u.toAdd v.toAdd hu hv
  exact ⟨g,hg⟩

theorem tetradPoint_no_faithful_eight (i : HexIndex) (X : Type*) [Finite X]
    [MulAction (TetradPointStabilizer i) X] [FaithfulSMul (TetradPointStabilizer i) X]
    (hx : Nat.card X = 8) : False := by
  let e := tetradPointStabilizerEquiv i
  letI : MulAction (TetradPointAffine i) X := MulAction.compHom X e.toMonoidHom
  haveI : FaithfulSMul (TetradPointAffine i) X := ⟨fun {g h} he =>
    e.injective (eq_of_smul_eq_smul (α := X) he)⟩
  exact tetradAffine_no_faithful_eight i X hx

theorem tetradPoint_no_injective_perm_eight (i : HexIndex)
    (ρ : TetradPointStabilizer i →* Equiv.Perm (Fin 8)) : ¬ Function.Injective ρ := by
  intro hρ
  letI : MulAction (TetradPointStabilizer i) (Fin 8) := MulAction.compHom (Fin 8) ρ
  haveI : FaithfulSMul (TetradPointStabilizer i) (Fin 8) := ⟨fun {g h} he =>
    hρ (Equiv.ext he)⟩
  exact tetradPoint_no_faithful_eight i (Fin 8) (by simp)

end Atlas.Codes
