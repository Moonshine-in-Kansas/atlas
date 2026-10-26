import Atlas.LinearGroups.ReeF4.IntrinsicGroup

/-! Intrinsic special vectors for the Ree–Tits geometry. This is the additional
partial-product condition, not merely the Albert rank-one condition.
No transitivity or counting assertion is made here. -/
noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A nonzero representative of an intrinsic special point. -/
def IsSpecialVector (m : ℕ) (u : TraceZero F) : Prop :=
  u ≠ 0 ∧ ∃ v : TraceZero F, ∃ h : StarDomain u v,
    u = proposedPartialProduct (thetaInv F m).toRingHom u v h

theorem IsSpecialVector.ne_zero {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u) : u ≠ 0 := hu.1

theorem IsSpecialVector.smul {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) {u : TraceZero F}
    (hu : IsSpecialVector m u) (a : F) (ha : a ≠ 0) :
    IsSpecialVector m (a • u) := by
  rcases hu with ⟨hu, v, huv, he⟩
  refine ⟨smul_ne_zero ha hu, (theta F m a / a) • v,
    starDomain_smul_right _ (starDomain_smul_left a huv), ?_⟩
  rw [proposedPartialProduct_smul (thetaInv F m).toRingHom a (theta F m a / a) u v huv]
  have hab : a * (theta F m a / a) = theta F m a := by
    calc
      a * (theta F m a / a) = theta F m a * (a*a⁻¹) := by
        rw [div_eq_mul_inv]
        ac_rfl
      _ = theta F m a := by rw [mul_inv_cancel₀ ha,mul_one]
  rw [hab]
  have ht : (thetaInv F m).toRingHom (theta F m a) = a := thetaInv_theta hcard a
  rw [ht, ← he]

theorem isSpecialVector_smul_iff {m : ℕ}
    (hcard : Nat.card F = 2^(2*m+1)) (a : F) (ha : a ≠ 0) (u : TraceZero F) :
    IsSpecialVector m (a • u) ↔ IsSpecialVector m u := by
  constructor
  · intro h
    have hi := h.smul hcard a⁻¹ (inv_ne_zero ha)
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hi
  · intro h
    exact h.smul hcard a ha

/-- Representative invariance only needs the inverse twist to be an equivalence;
the field-size hypothesis identifies this compensator with the source's θ(a)/a. -/
theorem IsSpecialVector.smul_intrinsic {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u) (a : F) (ha : a ≠ 0) :
    IsSpecialVector m (a • u) := by
  rcases hu with ⟨hu,v,huv,he⟩
  let b := (thetaInv F m).symm a / a
  refine ⟨smul_ne_zero ha hu,b • v,
    starDomain_smul_right b (starDomain_smul_left a huv),?_⟩
  rw [proposedPartialProduct_smul (thetaInv F m).toRingHom a b u v huv]
  have hab : a*b = (thetaInv F m).symm a := by
    dsimp only [b]
    calc
      a * ((thetaInv F m).symm a / a) = (thetaInv F m).symm a * (a*a⁻¹) := by
        rw [div_eq_mul_inv]
        ac_rfl
      _ = (thetaInv F m).symm a := by rw [mul_inv_cancel₀ ha,mul_one]
  rw [hab]
  have ht : (thetaInv F m).toRingHom ((thetaInv F m).symm a) = a :=
    (thetaInv F m).apply_symm_apply a
  rw [ht,←he]

theorem isSpecialVector_units_smul_iff (m : ℕ) (a : Fˣ) (u : TraceZero F) :
    IsSpecialVector m (a • u) ↔ IsSpecialVector m u := by
  simp only [Units.smul_def]
  constructor
  · intro h
    have hi := h.smul_intrinsic (a : F)⁻¹ (inv_ne_zero a.ne_zero)
    simpa only [smul_smul,inv_mul_cancel₀ a.ne_zero,one_smul] using hi
  · intro h
    exact h.smul_intrinsic (a : F) a.ne_zero

theorem IsSpecialVector.map_model {m : ℕ} {u : TraceZero F}
    (hu : IsSpecialVector m u) (g : Model F m) :
    IsSpecialVector m (g.val u) := by
  rcases hu with ⟨hu, v, huv, he⟩
  obtain ⟨hp,hg⟩ := (mem_modelSubgroup_iff m g.val).mp g.property
  have hd := (starDomain_polynomialStabilizer_iff ⟨g.val,hp⟩ u v).mpr huv
  refine ⟨?_,g.val v,hd,?_⟩
  · intro h
    apply hu
    apply g.val.injective
    simpa only [map_zero] using h
  · calc
      g.val u = g.val (proposedPartialProduct (thetaInv F m).toRingHom u v huv) :=
        congrArg g.val he
      _ = proposedPartialProduct (thetaInv F m).toRingHom (g.val u) (g.val v) hd :=
        (hg u v huv).symm

theorem isSpecialVector_model_iff {m : ℕ} (g : Model F m) (u : TraceZero F) :
    IsSpecialVector m (g.val u) ↔ IsSpecialVector m u := by
  constructor
  · intro h
    have hi := h.map_model g⁻¹
    change IsSpecialVector m (g.val.symm (g.val u)) at hi
    simpa only [LinearEquiv.symm_apply_apply] using hi
  · intro h
    exact h.map_model g

end Atlas.ReeF4
