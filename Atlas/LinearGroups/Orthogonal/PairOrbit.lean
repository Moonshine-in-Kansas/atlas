import Atlas.LinearGroups.Orthogonal.PairStabilizer
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Hyperbolic-pair orbit–stabilizer for the full quadratic isometry group -/
noncomputable section
namespace Atlas.Orthogonal
open Atlas.Quadratic
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

def hyperbolicPairs := {p : V × V // Q p.1 = 0 ∧ Q p.2 = 0 ∧ Q.polarBilin p.1 p.2 = 1}

instance hyperbolicPairsAction : MulAction (isometrySubgroup Q) (hyperbolicPairs Q) where
  smul g p := ⟨(g.val p.val.1, g.val p.val.2),
    (g.prop _).trans p.prop.1, (g.prop _).trans p.prop.2.1,
    (isometry_polar Q (isometryCarrierEquiv Q g) _ _).trans p.prop.2.2⟩
  one_smul p := rfl
  mul_smul g h p := rfl

theorem hyperbolicPairs_pretransitive (hQ : Q.radical = ⊥) :
    MulAction.IsPretransitive (isometrySubgroup Q) (hyperbolicPairs Q) where
  exists_smul_eq p r := by
    obtain ⟨g, hg, hk⟩ := exists_isometry_hyperbolic_pair Q hQ p.val.1 p.val.2 r.val.1 r.val.2
      p.prop.1 p.prop.2.1 r.prop.1 r.prop.2.1 p.prop.2.2 r.prop.2.2
    refine ⟨(isometryCarrierEquiv Q).symm g, Subtype.ext (Prod.ext hg hk)⟩

theorem hyperbolicPairs_stabilizer (p : hyperbolicPairs Q) :
    MulAction.stabilizer (isometrySubgroup Q) p = pairStabilizer Q p.val.1 p.val.2 := by
  ext g
  change (⟨(g.val p.val.1, g.val p.val.2), _⟩ : hyperbolicPairs Q) = p ↔ _
  constructor
  · intro h
    exact Prod.ext_iff.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Prod.ext h.1 h.2)

/-- Full group cardinality is the pair count times the complete complement group. -/
theorem card_isometry_eq_pairs_mul_complement (hQ : Q.radical = ⊥)
    (p : hyperbolicPairs Q) :
    Nat.card (isometrySubgroup Q) = Nat.card (hyperbolicPairs Q) *
      Nat.card (isometrySubgroup (complementForm Q p.val.1 p.val.2)) := by
  letI := hyperbolicPairs_pretransitive Q hQ
  have ho : Nat.card (MulAction.orbit (isometrySubgroup Q) p) = Nat.card (hyperbolicPairs Q) := by
    rw [MulAction.orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ _)
  have hs : Nat.card (MulAction.stabilizer (isometrySubgroup Q) p) =
      Nat.card (isometrySubgroup (complementForm Q p.val.1 p.val.2)) := by
    rw [hyperbolicPairs_stabilizer]
    exact Nat.card_congr (pairStabilizerEquiv Q _ _ p.prop.1 p.prop.2.1 p.prop.2.2).toEquiv
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (isometrySubgroup Q) p)
  rw [Nat.card_prod, ho, hs] at hc
  exact hc.symm

end Atlas.Orthogonal
