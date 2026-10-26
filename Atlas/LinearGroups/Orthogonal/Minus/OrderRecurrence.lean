import Atlas.LinearGroups.Orthogonal.Minus.StandardComplement
import Atlas.LinearGroups.Orthogonal.Minus.PairCount
import Atlas.LinearGroups.Orthogonal.IsometryTransport

/-! Full minus orthogonal pair stabilizers and their order recurrence. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

def standardPair (hdeg : Module.finrank F K = 2) (k : ℕ) :
    hyperbolicPairs (form hdeg (k+1)) :=
  ⟨((e 0,0),(f 0,0)),by simp only [form_apply,formD_e,← normForm_apply hdeg,map_zero,add_zero],by simp only [form_apply,formD_f,← normForm_apply hdeg,map_zero,add_zero],by simp only [polar_f0,e,Pi.single_eq_same]⟩

def standardPairStabilizer (hdeg : Module.finrank F K = 2) (k : ℕ) :
    pairStabilizer (form hdeg (k+1)) (e 0,0) (f 0,0) ≃* O hdeg k :=
  (pairStabilizerEquiv _ _ _ (standardPair hdeg k).prop.1
    (standardPair hdeg k).prop.2.1 (standardPair hdeg k).prop.2.2).trans
      (isometryGroupTransport (standardComplement hdeg))

theorem card_full_succ (hdeg : Module.finrank F K = 2) (k : ℕ) :
    Nat.card (O hdeg (k+1)) =
      ((Nat.card F^(k+2)+1)*(Nat.card F^(k+1)-1)*Nat.card F^(2*(k+1))) *
        Nat.card (O hdeg k) := by
  have h := card_isometry_eq_pairs_mul_complement (form hdeg (k+1))
    (radical_eq_bot hdeg (k+1)) (standardPair hdeg k)
  have hc := Nat.card_congr (isometryGroupTransport (standardComplement hdeg (n := k))).toEquiv
  change Nat.card (O hdeg (k+1)) = Nat.card (hyperbolicPairs (form hdeg (k+1))) *
    Nat.card (isometrySubgroup (Atlas.Quadratic.complementForm (form hdeg (k+1)) (e 0,0) (f 0,0))) at h
  rw [hc,card_hyperbolicPairs] at h
  exact h
end Atlas.Orthogonal.Minus
