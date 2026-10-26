import Atlas.LinearGroups.Chevalley.RootData.F4ShortOrbit
import Atlas.LinearGroups.Chevalley.RootData.DominantFunctionalStabilizer

/-! The short-axis stabilizer is the actual marked B3 parabolic of F4.
The dominant functional is the coroot of the literal short seed, hence it
vanishes on exactly the first three simple roots. No subgroup-order argument
or B3 recognition is used; a length-preserving B3 equivalence remains separate. -/
noncomputable section
namespace Atlas.Chevalley.F4ShortOrbit
open Classical RootData F4Data

def J : Finset base.support := Finset.univ.erase (baseIndexEquiv 3)

def seedFunctional : pairing.rootSpan ℤ →+ ℚ where
  toFun x := ((pairing.coroot seed) x.val : ℚ)
  map_zero' := by simp
  map_add' x y := by simp

theorem seedFunctional_simple (i : Fin 4) :
    seedFunctional (pairing.rootSpanMem ℤ (baseIndexEquiv i).val) =
      if i = 3 then 1 else 0 := by
  have h : ∀ i : Fin 4, F4Table.dot (F4Table.dualCoordinates 24)
      (F4Table.coordinates (F4Table.simpleIndex i)) = if i = 3 then 1 else 0 := by
    decide +kernel
  change (F4Table.dot (F4Table.dualCoordinates 24)
    (F4Table.coordinates (F4Table.simpleIndex i)) : ℚ) = _
  rw [h]
  split_ifs <;> norm_num

theorem seedFunctional_zero_simple :
    rootFunctionalZeroSimple pairing base seedFunctional = J := by
  ext i
  obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
  simp only [rootFunctionalZeroSimple, Finset.mem_filter, Finset.mem_univ,
    true_and, seedFunctional_simple, J, Finset.mem_erase, and_true]
  simp only [baseIndexEquiv.injective.ne_iff]
  split_ifs <;> simp_all

private theorem seedFunctional_root (β : F4Data.Root) :
    seedFunctional (pairing.rootSpanMem ℤ β) = (pairing.pairing β seed : ℚ) := rfl

private theorem weyl_pairing (w : W) (α β : F4Data.Root) :
    pairing.pairing (w.val α) (w.val β) = pairing.pairing α β := by
  obtain ⟨g, hg⟩ := w.property
  have hp := g.val.toHom.pairing (i := α) (j := β)
  change pairing.pairing (pairing.weylGroupToPerm g α)
    (pairing.weylGroupToPerm g β) = _ at hp
  simpa only [hg] using hp

private theorem pairing_detects_seed (β : F4Data.Root)
    (h : ∀ α, pairing.pairing α β = pairing.pairing α seed) : β = seed := by
  apply pairing.coroot.injective
  apply (Pi.basisFun ℤ (Fin 4)).ext
  intro k
  rw [Pi.basisFun_apply]
  have hk : pairing.root (F4Table.simpleIndex k) = Pi.single k 1 :=
    F4Table.simple_coordinates k
  rw [← hk]
  exact h (F4Table.simpleIndex k)

/-- This fixes the literal root label, not merely its norm or orbit cardinality. -/
theorem fixes_seed_iff_parabolic (w : W) :
    w.val seed = seed ↔ w ∈ rootParabolicSubgroup pairing base J := by
  have hdom : ∀ i : base.support,
      0 ≤ seedFunctional (pairing.rootSpanMem ℤ i.val) := by
    intro i
    obtain ⟨k, rfl⟩ := baseIndexEquiv.surjective i
    rw [seedFunctional_simple]
    split_ifs <;> norm_num
  have heq := rootFunctionalStabilizer_eq_parabolic pairing base seedFunctional hdom
  rw [seedFunctional_zero_simple] at heq
  rw [← heq]
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

end Atlas.Chevalley.F4ShortOrbit
