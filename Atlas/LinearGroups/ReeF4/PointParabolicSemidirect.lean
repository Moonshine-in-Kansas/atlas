import Atlas.LinearGroups.ReeF4.TailChartAction
import Atlas.LinearGroups.ReeF4.RootSuzukiScalarOrder
import Atlas.GroupTheory.NormalizerJoin

/-!
Source-only draft, 27 October 2026. No Lean, Lake, checker or audit was run.
The F4Work import refers to the parent's staged chart-action draft. Its tail
dependency has a passed checkpoint, but the rho/Levi/chart continuation remains
unverified; the Levi attempt was memory-stopped, not a Lean failure.

The parabolic here is literally the first special-point stabilizer. Opposite
chart transport and the existing actual pair-stabilizer recognition prove its
factorization; these conclusions are not supplied as hypotheses. The resulting
semidirect equivalence uses multiplication in Model and conjugation on the
actual seven-factor tail. The order follows from the two factor orders.
All statements include q=2. No full-group order, simplicity or Tits comparison
is asserted or used explicitly in the new proofs.
-/

noncomputable section
namespace Atlas.ReeF4

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The literal stabilizer of the marked first special point. -/
def firstPointParabolic (m : ℕ) : Subgroup (Model F m) :=
  MulAction.stabilizer (Model F m) (firstSpecialPoint (F := F) m)

theorem positiveRootTail_le_firstPointParabolic {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ≤ firstPointParabolic (F := F) m :=
  positiveRootTail_le_firstPointStabilizer hcard

theorem modelSuzukiProduct_le_firstPointParabolic {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    modelSuzukiProductSubgroup hcard ≤ firstPointParabolic (F := F) m := by
  rintro g ⟨⟨s,c⟩,rfl⟩
  exact MulAction.mem_stabilizer_iff.mpr (modelSuzukiProduct_fixes_first hcard s c)

/-- Match the image of the opposite point by a tail element. The residual
fixes both marked points, so actual pair-stabilizer recognition places it in L. -/
theorem firstPointParabolic_factorization {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (g : firstPointParabolic (F := F) m) :
    ∃ (r : positiveRootTailSubgroup hcard) (l : modelSuzukiProductSubgroup hcard),
      r.val * l.val = g.val := by
  have hg : g.val • firstSpecialPoint (F := F) m = firstSpecialPoint m :=
    MulAction.mem_stabilizer_iff.mp g.property
  let p : OppositeSpecialPoints (F := F) m :=
    ⟨oppositeSpecialPoint m, first_opposite_specialOpposite m⟩
  let q : OppositeSpecialPoints (F := F) m :=
    ⟨g.val • oppositeSpecialPoint m, by
      have h := (specialOpposite_model_iff m g.val
        (firstSpecialPoint m) (oppositeSpecialPoint m)).mpr
          (first_opposite_specialOpposite m)
      simpa only [hg] using h⟩
  obtain ⟨r,hr⟩ := positiveRootTail_oppositePoint_transitive hcard p q
  have hrp : r.val • oppositeSpecialPoint m = g.val • oppositeSpecialPoint m :=
    congrArg Subtype.val hr
  have hres : r.val⁻¹ * g.val ∈ modelSuzukiProductSubgroup hcard := by
    rw [oppositePairStabilizer_eq_suzukiProduct hcard]
    apply (mem_baseSpecialOppositePair_stabilizer_iff _).mpr
    constructor
    · exact MulAction.mem_stabilizer_iff.mp
        ((firstPointParabolic (F := F) m).mul_mem
          ((firstPointParabolic (F := F) m).inv_mem
            (positiveRootTail_le_firstPointParabolic hcard r.property)) g.property)
    · rw [mul_smul, ← hrp, inv_smul_smul]
  refine ⟨r, ⟨r.val⁻¹ * g.val, hres⟩, ?_⟩
  exact mul_inv_cancel_left r.val g.val

/-- Both inclusions in the full first-point stabilizer, with no generation premise. -/
theorem positiveRootTail_sup_suzukiProduct_eq_firstPointParabolic {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ⊔ modelSuzukiProductSubgroup hcard =
      firstPointParabolic (F := F) m := by
  apply le_antisymm
  · exact sup_le (positiveRootTail_le_firstPointParabolic hcard)
      (modelSuzukiProduct_le_firstPointParabolic hcard)
  · intro g hg
    obtain ⟨r,l,hrl⟩ := firstPointParabolic_factorization hcard ⟨g,hg⟩
    change r.val * l.val = g at hrl
    rw [← hrl]
    exact Subgroup.mul_mem_sup r.property l.property

theorem firstPointParabolic_existsUnique {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (g : firstPointParabolic (F := F) m) :
    ∃! p : positiveRootTailSubgroup hcard × modelSuzukiProductSubgroup hcard,
      p.1.val * p.2.val = g.val := by
  obtain ⟨r,l,hrl⟩ := firstPointParabolic_factorization hcard g
  refine ⟨(r,l), hrl, ?_⟩
  intro p hp
  exact Subgroup.mul_injective_of_disjoint
    (positiveRootTail_disjoint_suzukiProduct hcard) (hp.trans hrl.symm)

theorem firstPointParabolic_le_tail_normalizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    firstPointParabolic (F := F) m ≤
      Subgroup.normalizer (positiveRootTailSubgroup hcard) := by
  rw [← positiveRootTail_sup_suzukiProduct_eq_firstPointParabolic hcard]
  exact sup_le (positiveRootTailSubgroup hcard).le_normalizer
    (modelSuzukiProduct_le_tail_normalizer hcard)

theorem positiveRootTail_normal_in_firstPointParabolic {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    ((positiveRootTailSubgroup hcard).subgroupOf
      (firstPointParabolic (F := F) m)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (positiveRootTail_le_firstPointParabolic hcard)).mpr
      (firstPointParabolic_le_tail_normalizer hcard)

/-- The internal semidirect product maps to the full parabolic by (r,l) ↦ rl. -/
def tailLeviPointParabolicEquiv {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ⋊[suzukiProductTailAction hcard]
      modelSuzukiProductSubgroup hcard ≃* firstPointParabolic (F := F) m :=
  (Atlas.GroupTheory.normalizerJoinMulEquiv
    (positiveRootTailSubgroup hcard) (modelSuzukiProductSubgroup hcard)
    (modelSuzukiProduct_le_tail_normalizer hcard)
    (positiveRootTail_disjoint_suzukiProduct hcard)).trans
      (MulEquiv.subgroupCongr
        (positiveRootTail_sup_suzukiProduct_eq_firstPointParabolic hcard))

@[simp] theorem tailLeviPointParabolicEquiv_apply {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (x : positiveRootTailSubgroup hcard ⋊[suzukiProductTailAction hcard]
      modelSuzukiProductSubgroup hcard) :
    (tailLeviPointParabolicEquiv hcard x).val = x.left.val * x.right.val := rfl

/-- Transport actual conjugation along the existing injective Suzuki × units embedding. -/
def suzukiScalarTailAction {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    (SuzukiFamily.Group F m × Fˣ) →* MulAut (positiveRootTailSubgroup hcard) :=
  (suzukiProductTailAction hcard).comp (modelSuzukiProductEquiv hcard).toMonoidHom

theorem suzukiScalarTailAction_apply {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (s : SuzukiFamily.Group F m × Fˣ) (r : positiveRootTailSubgroup hcard) :
    (suzukiScalarTailAction hcard s r).val =
      modelSuzukiProductHom hcard s * r.val * (modelSuzukiProductHom hcard s)⁻¹ := rfl

def tailSuzukiScalarSemidirectEquiv {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ⋊[suzukiScalarTailAction hcard]
      (SuzukiFamily.Group F m × Fˣ) ≃*
    positiveRootTailSubgroup hcard ⋊[suzukiProductTailAction hcard]
      modelSuzukiProductSubgroup hcard :=
  SemidirectProduct.congr (MulEquiv.refl (positiveRootTailSubgroup hcard))
    (modelSuzukiProductEquiv hcard) (by
      intro s
      apply MulEquiv.ext
      intro r
      rfl)

/-- The concrete semidirect description of the actual first-point stabilizer. -/
def pointParabolicSemidirectEquiv {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ⋊[suzukiScalarTailAction hcard]
      (SuzukiFamily.Group F m × Fˣ) ≃* firstPointParabolic (F := F) m :=
  (tailSuzukiScalarSemidirectEquiv hcard).trans (tailLeviPointParabolicEquiv hcard)

/-- The isomorphism uses the specified actual operators, not an order comparison. -/
@[simp] theorem pointParabolicSemidirectEquiv_apply {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (x : positiveRootTailSubgroup hcard ⋊[suzukiScalarTailAction hcard]
      (SuzukiFamily.Group F m × Fˣ)) :
    (pointParabolicSemidirectEquiv hcard x).val =
      x.left.val * modelSuzukiProductHom hcard x.right := rfl

@[simp] theorem pointParabolicSemidirectEquiv_inl {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (r : positiveRootTailSubgroup hcard) :
    (pointParabolicSemidirectEquiv hcard (SemidirectProduct.inl r)).val = r.val := by
  rw [pointParabolicSemidirectEquiv_apply]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]

@[simp] theorem pointParabolicSemidirectEquiv_inr {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (s : SuzukiFamily.Group F m × Fˣ) :
    (pointParabolicSemidirectEquiv hcard (SemidirectProduct.inr s)).val =
      modelSuzukiProductHom hcard s := by
  rw [pointParabolicSemidirectEquiv_apply]
  simp only [SemidirectProduct.left_inr, SemidirectProduct.right_inr,
    Subgroup.coe_one, one_mul]

/-- Order from the actual semidirect equivalence and the factor orders only. -/
theorem card_firstPointParabolic {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Nat.card (firstPointParabolic (F := F) m) =
      (Nat.card F)^12 * ((Nat.card F)^2 + 1) * (Nat.card F - 1)^2 := by
  rw [← Nat.card_congr (tailLeviPointParabolicEquiv hcard).toEquiv,
    SemidirectProduct.card, card_positiveRootTailSubgroup hcard,
    card_modelSuzukiProductSubgroup hcard]
  ring

theorem card_firstPointParabolic_binary
    (hcard : Nat.card F = 2 ^ (2 * 0 + 1)) :
    Nat.card (firstPointParabolic (F := F) 0) = 20480 := by
  rw [card_firstPointParabolic hcard, hcard]
  norm_num

end Atlas.ReeF4
