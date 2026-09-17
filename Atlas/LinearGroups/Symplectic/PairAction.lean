import Atlas.LinearGroups.Symplectic.PairCount
import Atlas.LinearGroups.Symplectic.PairStabilizer
import Mathlib.GroupTheory.GroupAction.Quotient

noncomputable section
namespace Atlas.Symplectic
variable {n : ℕ} {F : Type*} [Field F]

instance pairAction : MulAction (Sp n F) (HyperbolicPairs n F) where
  smul g p := ⟨(g • p.val.1,g • p.val.2), by
    rw [smul_eq_mulVec, smul_eq_mulVec, preserves]; exact p.prop⟩
  one_smul p := by
    apply Subtype.ext
    change ((1 : Sp n F) • p.val.1, (1 : Sp n F) • p.val.2) = p.val
    simp
  mul_smul g h p := by
    apply Subtype.ext
    change ((g*h) • p.val.1,(g*h) • p.val.2) = (g • (h • p.val.1),g • (h • p.val.2))
    simp only [mul_smul]

def standardPair (n : ℕ) (F : Type*) [Field F] : HyperbolicPairs (n+1) F :=
  ⟨(e 0,f 0),by simp [e,Pi.single_apply]⟩

/-- Full pair transitivity follows from the independent alternating-basis theorem. -/
theorem exists_pair_transporter (p : HyperbolicPairs (n+1) F) :
    ∃ g : Sp (n+1) F, g • standardPair n F = p := by
  obtain ⟨k,hk₁,hk₂⟩ := exists_isometry_pair n form form_alternating form_nondegenerate
    vector_finrank p.val.1 p.val.2 p.prop
  refine ⟨ofLinear k.symm.toLinearEquiv k.symm.map_app', ?_⟩
  apply Subtype.ext
  change (ofLinear _ _ • e 0, ofLinear _ _ • f 0) = p.val
  simp only [ofLinear_apply]
  apply Prod.ext
  · rw [← hk₁]; exact k.symm_apply_apply _
  · rw [← hk₂]; exact k.symm_apply_apply _

theorem standardPair_stabilizer :
    MulAction.stabilizer (Sp (n+1) F) (standardPair n F) = pairStabilizer n F := by
  ext g
  rw [mem_pairStabilizer]
  change (g • standardPair n F = standardPair n F) ↔ _
  rw [Subtype.ext_iff]
  exact Prod.ext_iff

/-- The actual ordered-pair orbit is the whole normalized-pair geometry. -/
def standardPairOrbitEquiv : MulAction.orbit (Sp (n+1) F) (standardPair n F) ≃
    HyperbolicPairs (n+1) F :=
  Equiv.ofBijective (fun p => p.val) ⟨Subtype.val_injective, fun p =>
    ⟨⟨p,by obtain ⟨g,hg⟩ := exists_pair_transporter p; exact ⟨g,hg⟩⟩,rfl⟩⟩

/-- Independent order recurrence using the full pointwise hyperbolic-pair stabilizer. -/
theorem card_sp_succ [Finite F] : Nat.card (Sp (n+1) F) =
    (Nat.card F ^ (2*(n+1))-1) * Nat.card F ^ (2*n+1) * Nat.card (Sp n F) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Sp (n+1) F)
    (standardPair n F)), Nat.card_prod,
    Nat.card_congr standardPairOrbitEquiv, standardPair_stabilizer,
    Nat.card_congr pairStabilizerEquiv.toEquiv, hyperbolicPairs_card]
  congr 2

end Atlas.Symplectic
