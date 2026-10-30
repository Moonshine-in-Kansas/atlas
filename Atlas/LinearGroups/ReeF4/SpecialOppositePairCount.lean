import Atlas.LinearGroups.ReeF4.PositiveRootOppositeTransitivity
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Pair counting and orbit–stabilizer, without any identification or order
assumption for the full opposite-pair stabilizer. -/
noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

abbrev OppositeFiber (m : ℕ) (p : SpecialPoints (F := F) m) :=
  {q : SpecialPoints (F := F) m // SpecialOpposite m p q}

def oppositeFiberEquiv {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : SpecialPoints (F := F) m) : OppositeFiber m p ≃ OppositeSpecialPoints (F := F) m := by
  classical
  let g := Classical.choose (elementary_specialPoint_transitive hcard p (firstSpecialPoint m))
  have hg : g.val • p=firstSpecialPoint m :=
    Classical.choose_spec (elementary_specialPoint_transitive hcard p (firstSpecialPoint m))
  have hi : g.val⁻¹ • firstSpecialPoint m=p := by rw [←hg,inv_smul_smul]
  exact
    { toFun := fun q => ⟨g.val • q.val,by
        have h := (specialOpposite_model_iff m g.val p q.val).mpr q.property
        simpa only [hg] using h⟩
      invFun := fun q => ⟨g.val⁻¹ • q.val,by
        have h := (specialOpposite_model_iff m g.val⁻¹ (firstSpecialPoint m) q.val).mpr q.property
        simpa only [hi] using h⟩
      left_inv := fun q => Subtype.ext (inv_smul_smul g.val q.val)
      right_inv := fun q => Subtype.ext (smul_inv_smul g.val q.val) }

def specialOppositePairsEquivSigma (m : ℕ) :
    SpecialOppositePairs (F := F) m ≃ ((p : SpecialPoints (F := F) m) × OppositeFiber m p) where
  toFun pq := ⟨pq.val.1,⟨pq.val.2,pq.property⟩⟩
  invFun pq := ⟨(pq.1,pq.2.val),pq.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_oppositeFiber {m : ℕ} (hcard : Nat.card F=2^(2*m+1))
    (p : SpecialPoints (F := F) m) : Nat.card (OppositeFiber m p)=(Nat.card F)^10 := by
  rw [Nat.card_congr (oppositeFiberEquiv hcard p),card_oppositeSpecialPoints hcard]

theorem card_specialOppositePairs {m : ℕ} (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (SpecialOppositePairs (F := F) m)=
      ((Nat.card F)^6+1)*((Nat.card F)^3+1)*(Nat.card F+1)*(Nat.card F)^10 := by
  classical
  letI : Fintype (SpecialPoints (F := F) m) := Fintype.ofFinite _
  letI : ∀ p : SpecialPoints (F := F) m, Finite (OppositeFiber m p) :=
    fun _ => by unfold OppositeFiber; infer_instance
  rw [Nat.card_congr (specialOppositePairsEquivSigma m),Nat.card_sigma]
  simp only [card_oppositeFiber hcard,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Nat.card_eq_fintype_card,card_specialPoints hcard]
  simp only [Nat.cast_id]

/-- The actual full intrinsic subgroup fixing the two marked projective points. -/
def fullOppositePairStabilizer (m : ℕ) : Subgroup (Model F m) :=
  MulAction.stabilizer (Model F m) (baseSpecialOppositePair (F := F) m)

theorem model_order_oppositePair_factorization {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1)) :
    Nat.card (Model F m)=
      (((Nat.card F)^6+1)*((Nat.card F)^3+1)*(Nat.card F+1)*(Nat.card F)^10) *
        Nat.card (fullOppositePairStabilizer (F := F) m) := by
  letI := model_specialOppositePairs_pretransitive hcard
  have ho : Nat.card (MulAction.orbit (Model F m) (baseSpecialOppositePair (F := F) m))=
      Nat.card (SpecialOppositePairs (F := F) m) := by
    rw [MulAction.orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ _)
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (Model F m) (baseSpecialOppositePair (F := F) m))
  rw [Nat.card_prod,ho,card_specialOppositePairs hcard] at h
  exact h.symm

/-- Only the still-independent full pair-stabilizer order is needed to finish
this order route. No such order or Suzuki identification is asserted here. -/
theorem model_order_of_fullPairStabilizer_order {m : ℕ}
    (hcard : Nat.card F=2^(2*m+1))
    (hstab : Nat.card (fullOppositePairStabilizer (F := F) m)=
      (Nat.card F)^2*((Nat.card F)^2+1)*(Nat.card F-1)^2) :
    Nat.card (Model F m)=
      (((Nat.card F)^6+1)*((Nat.card F)^3+1)*(Nat.card F+1)*(Nat.card F)^10) *
        ((Nat.card F)^2*((Nat.card F)^2+1)*(Nat.card F-1)^2) := by
  rw [model_order_oppositePair_factorization hcard,hstab]

end Atlas.ReeF4
