import Atlas.LinearGroups.ReeF4.PositiveRootTail
import Atlas.LinearGroups.ReeF4.TailLeviNormalization
import Atlas.LinearGroups.ReeF4.PositiveRootChartTransitivity
import Atlas.LinearGroups.ReeF4.PositiveRootPointAction
import Mathlib.SetTheory.Cardinal.Finite

/-!
Source-only draft, 27 October 2026. No Lean, Lake, audit or checker was run.
The FamilyWork imports designate the parent's staged copies of the preserved
tail and Levi-normalization drafts; no previous source is changed here.

The actual chart word belongs to the seven-factor tail R. It gives R-transitivity
on the opposite-point fibre. The two existing q^10 counts then make the actual
orbit map bijective, proving freeness and R intersect L = 1, including q=2.
No full-group order, parabolic decomposition, simplicity, or Tits comparison
is a hypothesis or conclusion.
-/

noncomputable section
namespace Atlas.ReeF4
open Atlas.Albert

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The chart word is the inverse of the old tail word with reversed parameters.
The group inverses are retained; no coordinate inverse formula is needed. -/
theorem chartUnipotentWord_eq_inverse_tailWord {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (a : Fin 4 → F) (p : Fin 3 → F × F) :
    chartUnipotentWord hcard a p =
      (positiveRootTailWord hcard ![a 3, a 2, a 1, a 0] ![p 2, p 1, p 0])⁻¹ := by
  unfold chartUnipotentWord
  rw [chartLongConjugate_eq_positive_0, chartLongConjugate_eq_positive_1,
    chartLongConjugate_eq_positive_2, chartLongConjugate_eq_positive_3,
    chartShortConjugate_eq_positive_0, chartShortConjugate_eq_positive_1,
    chartShortConjugate_eq_positive_2]
  simp only [positiveRootTailWord, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.reduceFinMk, mul_inv_rev, mul_assoc]
  rfl

theorem chartUnipotentWord_mem_tail {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (a : Fin 4 → F) (p : Fin 3 → F × F) :
    chartUnipotentWord hcard a p ∈ positiveRootTailSubgroup hcard := by
  rw [chartUnipotentWord_eq_inverse_tailWord]
  exact (positiveRootTailSubgroup hcard).inv_mem
    (positiveRootTailWord_mem hcard _ _)

theorem positiveRootTail_fixes_firstSpecialPoint {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : positiveRootTailSubgroup hcard) :
    g.val • firstSpecialPoint (F := F) m = firstSpecialPoint m :=
  positiveRootSubgroup_fixes_firstSpecialPoint hcard
    ⟨g.val, positiveRootTailSubgroup_le_positiveRootSubgroup hcard g.property⟩

theorem positiveRootTail_le_firstPointStabilizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ≤
      MulAction.stabilizer (Model F m) (firstSpecialPoint (F := F) m) := by
  intro g hg
  exact MulAction.mem_stabilizer_iff.mpr
    (positiveRootTail_fixes_firstSpecialPoint hcard ⟨g,hg⟩)

/-- Reuse the seven chart pivots and their existing factorization in G. -/
theorem positiveRootTail_chart9_orbit {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (z : NormalizedSpecialChart (F := F) m 9) :
    ∃ g : positiveRootTailSubgroup hcard,
      g.val.val (rootVector (0,7)) = z.val := by
  obtain ⟨a,p,hz⟩ := chart9_transport_exists hcard z
  refine ⟨⟨chartUnipotentWord hcard a p, chartUnipotentWord_mem_tail hcard a p⟩, ?_⟩
  rw [chartTransportProduct_factorization, modelProduct_apply, chartFinalWeyl_root] at hz
  exact hz

/-- Transitivity already holds for the actual normalized vectors. -/
theorem positiveRootTail_chart9_transitive {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (z z' : NormalizedSpecialChart (F := F) m 9) :
    ∃ g : positiveRootTailSubgroup hcard, g.val.val z.val = z'.val := by
  obtain ⟨u,hu⟩ := positiveRootTail_chart9_orbit hcard z
  obtain ⟨v,hv⟩ := positiveRootTail_chart9_orbit hcard z'
  refine ⟨v * u⁻¹, ?_⟩
  rw [← hu]
  change v.val.val (u.val.val.symm (u.val.val (rootVector (0,7)))) = z'.val
  rw [LinearEquiv.symm_apply_apply]
  exact hv

/-- Restrict the actual special-point action to the tail and the opposite fibre. -/
instance positiveRootTailOppositeAction {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    MulAction (positiveRootTailSubgroup hcard) (OppositeSpecialPoints (F := F) m) where
  smul g p := ⟨g.val • p.val, by
    have h := (specialOpposite_model_iff m g.val (firstSpecialPoint m) p.val).mpr p.property
    simpa only [positiveRootTail_fixes_firstSpecialPoint hcard g] using h⟩
  one_smul p := Subtype.ext (one_smul (Model F m) p.val)
  mul_smul g h p := Subtype.ext (mul_smul g.val h.val p.val)

@[simp] theorem positiveRootTailOppositeAction_val {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (g : positiveRootTailSubgroup hcard) (p : OppositeSpecialPoints (F := F) m) :
    (g • p).val = g.val • p.val := rfl

theorem positiveRootTail_oppositePoint_transitive {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (p q : OppositeSpecialPoints (F := F) m) :
    ∃ g : positiveRootTailSubgroup hcard, g • p = q := by
  obtain ⟨u,rfl⟩ := chart9ToOpposite_surjective m p
  obtain ⟨v,rfl⟩ := chart9ToOpposite_surjective m q
  obtain ⟨g,hg⟩ := positiveRootTail_chart9_transitive hcard u v
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change g.val • specialPointMk m u.val u.property.1 =
    specialPointMk m v.val v.property.1
  simp only [specialPointMk_smul, hg]

theorem positiveRootTail_oppositePoint_pretransitive {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    MulAction.IsPretransitive (positiveRootTailSubgroup hcard)
      (OppositeSpecialPoints (F := F) m) where
  exists_smul_eq := positiveRootTail_oppositePoint_transitive hcard

/-- Cardinality is used only after surjectivity of this specified orbit map. -/
theorem positiveRootTail_oppositeOrbit_bijective {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (p : OppositeSpecialPoints (F := F) m) :
    Function.Bijective (fun g : positiveRootTailSubgroup hcard => g • p) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨fun q => positiveRootTail_oppositePoint_transitive hcard p q, ?_⟩
  rw [card_positiveRootTailSubgroup hcard, card_oppositeSpecialPoints hcard]

/-- An equivalence of sets given by the actual orbit map, for any base point in the fibre. -/
def positiveRootTailOppositeOrbitEquiv {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (p : OppositeSpecialPoints (F := F) m) :
    positiveRootTailSubgroup hcard ≃ OppositeSpecialPoints (F := F) m :=
  Equiv.ofBijective (fun g => g • p) (positiveRootTail_oppositeOrbit_bijective hcard p)

@[simp] theorem positiveRootTailOppositeOrbitEquiv_apply {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (p : OppositeSpecialPoints (F := F) m) (g : positiveRootTailSubgroup hcard) :
    positiveRootTailOppositeOrbitEquiv hcard p g = g • p := rfl

theorem positiveRootTail_oppositePoint_existsUnique {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (p q : OppositeSpecialPoints (F := F) m) :
    ∃! g : positiveRootTailSubgroup hcard, g • p = q := by
  obtain ⟨g,hg⟩ := positiveRootTail_oppositePoint_transitive hcard p q
  refine ⟨g,hg,?_⟩
  intro h hh
  exact (positiveRootTail_oppositeOrbit_bijective hcard p).injective (hh.trans hg.symm)

/-- Freeness concerns R on this fibre, not the action of the full intrinsic group. -/
theorem positiveRootTail_eq_one_of_fix_oppositePoint {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (p : OppositeSpecialPoints (F := F) m) (g : positiveRootTailSubgroup hcard)
    (hg : g • p = p) : g = 1 := by
  apply (positiveRootTail_oppositeOrbit_bijective hcard p).injective
  simpa only [one_smul] using hg

theorem positiveRootTail_oppositePoint_stabilizer_eq_bot {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (p : OppositeSpecialPoints (F := F) m) :
    MulAction.stabilizer (positiveRootTailSubgroup hcard) p = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  exact positiveRootTail_eq_one_of_fix_oppositePoint hcard p g
    (MulAction.mem_stabilizer_iff.mp hg)

theorem positiveRootTail_eq_one_of_fixes_oppositeSpecialPoint {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : positiveRootTailSubgroup hcard)
    (hg : g.val • oppositeSpecialPoint (F := F) m = oppositeSpecialPoint m) : g = 1 :=
  positiveRootTail_eq_one_of_fix_oppositePoint hcard
    ⟨oppositeSpecialPoint m, first_opposite_specialOpposite m⟩ g (Subtype.ext hg)

theorem positiveRootTail_inf_oppositePointStabilizer {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ⊓
      MulAction.stabilizer (Model F m) (oppositeSpecialPoint (F := F) m) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  rintro g ⟨hgR,hgp⟩
  exact congrArg Subtype.val
    (positiveRootTail_eq_one_of_fixes_oppositeSpecialPoint hcard ⟨g,hgR⟩
      (MulAction.mem_stabilizer_iff.mp hgp))

/-- Only the existing Levi's fixation of the opposite point is needed here. -/
theorem positiveRootTail_disjoint_suzukiProduct {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Disjoint (positiveRootTailSubgroup hcard) (modelSuzukiProductSubgroup hcard) := by
  apply Subgroup.disjoint_def.mpr
  intro g hgR hgL
  obtain ⟨⟨s,c⟩,rfl⟩ := hgL
  exact congrArg Subtype.val
    (positiveRootTail_eq_one_of_fixes_oppositeSpecialPoint hcard ⟨_,hgR⟩
      (modelSuzukiProduct_fixes_opposite hcard s c))

theorem positiveRootTail_inf_suzukiProduct {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    positiveRootTailSubgroup hcard ⊓ modelSuzukiProductSubgroup hcard = ⊥ :=
  (positiveRootTail_disjoint_suzukiProduct hcard).eq_bot

end Atlas.ReeF4
