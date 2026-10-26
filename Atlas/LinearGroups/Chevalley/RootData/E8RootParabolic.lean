import Atlas.LinearGroups.Chevalley.RootData.E8
import Atlas.LinearGroups.Chevalley.RootData.DominantFunctionalStabilizer
import Mathlib.Tactic.NormNum

/-! The stabilizer of the literal dominant E8 root is the actual parabolic
omitting node seven. The root orbit, the E7 Weyl embedding and the coset-length
histogram remain separate statements; no order or orbit recognition is used. -/
noncomputable section
set_option maxRecDepth 32768
namespace Atlas.Chevalley.E8Parabolic
open Classical E8Data RootData

/-- The dominant root in the existing 240-label integral E8 table. -/
def seed : Root := 238

theorem seed_coordinates :
    E8Table.coordinates seed = ![2, 3, 4, 6, 5, 4, 3, 2] := by
  decide +kernel

/-- The seven actual simple nodes other than node seven. -/
def J : Finset base.support := Finset.univ.erase (baseIndexEquiv 7)

def seedFunctional : pairing.rootSpan ℤ →+ ℚ where
  toFun x := ((pairing.coroot seed) x.val : ℚ)
  map_zero' := by simp
  map_add' x y := by simp

theorem seedFunctional_simple (i : Fin 8) :
    seedFunctional (pairing.rootSpanMem ℤ (baseIndexEquiv i).val) =
      if i = 7 then 1 else 0 := by
  have h : ∀ i : Fin 8,
      (∑ j, CartanMatrix.E 8 i j * E8Table.coordinates 238 j) =
        if i = 7 then 1 else 0 := by
    decide +kernel
  change (ExceptionalData.form 8 (E8Table.coordinates 238)
    (E8Table.coordinates (E8Table.simpleIndex i)) : ℚ) = _
  rw [E8Table.simple_coordinates, ExceptionalData.form_symm,
    ExceptionalData.form_single_left, h]
  split_ifs <;> norm_num

theorem seedFunctional_nonneg (i : base.support) :
    0 ≤ seedFunctional (pairing.rootSpanMem ℤ i.val) := by
  obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
  rw [seedFunctional_simple]
  split_ifs <;> norm_num

theorem seedFunctional_zero_simple :
    rootFunctionalZeroSimple pairing base seedFunctional = J := by
  ext i
  obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
  simp only [rootFunctionalZeroSimple, Finset.mem_filter, Finset.mem_univ,
    true_and, seedFunctional_simple, J, Finset.mem_erase, and_true]
  simp only [baseIndexEquiv.injective.ne_iff]
  split_ifs <;> simp_all

theorem seedFunctional_stabilizer :
    rootFunctionalStabilizer pairing seedFunctional =
      rootParabolicSubgroup pairing base J := by
  simpa only [seedFunctional_zero_simple] using
    rootFunctionalStabilizer_eq_parabolic pairing base seedFunctional
      seedFunctional_nonneg

private theorem seedFunctional_root (β : Root) :
    seedFunctional (pairing.rootSpanMem ℤ β) = (pairing.pairing β seed : ℚ) := rfl

private theorem weyl_pairing (w : pairing.weylGroupToPerm.range) (α β : Root) :
    pairing.pairing (w.val α) (w.val β) = pairing.pairing α β := by
  obtain ⟨g, hg⟩ := w.property
  have hp := g.val.toHom.pairing (i := α) (j := β)
  change pairing.pairing (pairing.weylGroupToPerm g α)
    (pairing.weylGroupToPerm g β) = _ at hp
  simpa only [hg] using hp

private theorem pairing_detects_seed (β : Root)
    (h : ∀ α, pairing.pairing α β = pairing.pairing α seed) : β = seed := by
  apply pairing.coroot.injective
  apply (Pi.basisFun ℤ (Fin 8)).ext
  intro k
  rw [Pi.basisFun_apply]
  have hk : pairing.root (E8Table.simpleIndex k) = Pi.single k 1 :=
    E8Table.simple_coordinates k
  rw [← hk]
  exact h (E8Table.simpleIndex k)

/-- Actual root-label stabilization, with no root-orbit cardinality premise. -/
theorem fixes_seed_iff_parabolic (w : pairing.weylGroupToPerm.range) :
    w.val seed = seed ↔ w ∈ rootParabolicSubgroup pairing base J := by
  rw [← seedFunctional_stabilizer]
  constructor
  · intro hw β
    rw [seedFunctional_root, seedFunctional_root]
    exact congrArg (fun z : ℤ => (z : ℚ)) (by
      simpa only [hw] using weyl_pairing w β seed)
  · intro hw
    apply pairing_detects_seed
    intro α
    have hfun := hw ((w⁻¹).val α)
    have hinv : w.val ((w⁻¹).val α) = α := w.val.apply_symm_apply α
    rw [seedFunctional_root, seedFunctional_root, hinv] at hfun
    have hcast : pairing.pairing α seed = pairing.pairing ((w⁻¹).val α) seed :=
      Int.cast_injective hfun
    have hp := weyl_pairing w ((w⁻¹).val α) seed
    rw [hinv] at hp
    exact hp.trans hcast.symm

end Atlas.Chevalley.E8Parabolic
