import Atlas.LinearGroups.Chevalley.RootData.ClassicalDSignedCoordinate
import Mathlib.SetTheory.Cardinal.Finite

/-! The actual Weyl orbit of the first-coordinate additive functional on the
D root lattice is exactly the 2r signed coordinate functionals. Representatives
are actual root-pairing automorphisms; equality on the root basis removes any
dependence on which representative of a root permutation was chosen. -/
noncomputable section
namespace Atlas.Chevalley.ClassicalDParabolic
open Classical ClassicalData RootData Integral.Minuscule.TypeD

def signedCoordinateFunctional (n : ℕ) (c : Fin (n + 3) × Bool) :
    (pairingD (n + 3)).rootSpan ℤ →+ ℚ where
  toFun x := (sign c.2 * x.val c.1 : ℤ)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

private theorem functional_ext_on_roots (n : ℕ)
    (f g : (pairingD (n + 3)).rootSpan ℤ →+ ℚ)
    (h : ∀ β, f ((pairingD (n + 3)).rootSpanMem ℤ β) =
      g ((pairingD (n + 3)).rootSpanMem ℤ β)) : f = g := by
  apply AddMonoidHom.toIntLinearMap_injective
  apply (baseD (n + 1)).toWeightBasisInt.ext
  intro i
  have hi : (baseD (n + 1)).toWeightBasisInt i =
      (pairingD (n + 3)).rootSpanMem ℤ i.val := by
    apply Subtype.ext
    exact (baseD (n + 1)).coe_toWeightBasisInt_apply i
  change f ((baseD (n + 1)).toWeightBasisInt i) = g ((baseD (n + 1)).toWeightBasisInt i)
  rw [hi]
  exact h i.val

/-- Pull back the first coordinate by an actual Weyl automorphism representing
the given actual root permutation. Only its restriction to the root span is used. -/
def coordinateFunctionalTranslate (n : ℕ)
    (w : (pairingD (n + 3)).weylGroupToPerm.range) :
    (pairingD (n + 3)).rootSpan ℤ →+ ℚ where
  toFun x := (((Classical.choose w.property) • x.val) 0 : ℚ)
  map_zero' := by simp
  map_add' x y := by simp [smul_add]

theorem coordinateFunctionalTranslate_root (n : ℕ)
    (w : (pairingD (n + 3)).weylGroupToPerm.range) (β : DRoot (n + 3)) :
    coordinateFunctionalTranslate n w ((pairingD (n + 3)).rootSpanMem ℤ β) =
      ((w.val β).val 0 : ℚ) := by
  change ((((Classical.choose w.property) • (pairingD (n + 3)).root β) 0 : ℤ) : ℚ) = _
  rw [(pairingD (n + 3)).weylGroup_apply_root, Classical.choose_spec w.property]
  rfl

/-- This equality also verifies that the arbitrary chosen lift acts canonically
on the restricted functional; no faithfulness on the full ambient lattice is used. -/
theorem coordinateFunctionalTranslate_one (n : ℕ) :
    coordinateFunctionalTranslate n 1 = coordinateFunctional n := by
  apply functional_ext_on_roots
  intro β
  exact coordinateFunctionalTranslate_root n 1 β

theorem coordinateFunctionalTranslate_signed (n : ℕ)
    (w : (pairingD (n + 3)).weylGroupToPerm.range) :
    ∃ c : Fin (n + 3) × Bool,
      coordinateFunctionalTranslate n w = signedCoordinateFunctional n c := by
  obtain ⟨c, hc⟩ := rootCoordinate_weyl n w (0, true)
  refine ⟨c, functional_ext_on_roots n _ _ ?_⟩
  intro β
  rw [coordinateFunctionalTranslate_root]
  have h : (w.val β).val 0 = rootCoordinate n c β := by
    simpa only [rootCoordinate, sign, ite_true, one_mul] using hc β
  exact congrArg (fun z : ℤ => (z : ℚ)) h

theorem signedCoordinateFunctional_reachable (n : ℕ) (c : Fin (n + 3) × Bool) :
    ∃ w : (pairingD (n + 3)).weylGroupToPerm.range,
      coordinateFunctionalTranslate n w = signedCoordinateFunctional n c := by
  obtain ⟨w, hw⟩ := rootCoordinate_reachable n c
  refine ⟨w, functional_ext_on_roots n _ _ ?_⟩
  intro β
  rw [coordinateFunctionalTranslate_root]
  exact congrArg (fun z : ℤ => (z : ℚ)) (hw β)

theorem signedCoordinateFunctional_injective (n : ℕ) :
    Function.Injective (signedCoordinateFunctional n) := by
  intro c d h
  apply rootCoordinate_injective n
  funext β
  apply Int.cast_injective (α := ℚ)
  exact congrArg (fun f : (pairingD (n + 3)).rootSpan ℤ →+ ℚ =>
    f ((pairingD (n + 3)).rootSpanMem ℤ β)) h

/-- The literal orbit, not an externally identified signed-coordinate model. -/
def CoordinateFunctionalOrbit (n : ℕ) := Set.range (coordinateFunctionalTranslate n)

def signedCoordinateOrbitEquiv (n : ℕ) :
    (Fin (n + 3) × Bool) ≃ CoordinateFunctionalOrbit n :=
  Equiv.ofBijective
    (fun c => ⟨signedCoordinateFunctional n c, signedCoordinateFunctional_reachable n c⟩)
    ⟨by
      intro c d h
      exact signedCoordinateFunctional_injective n (congrArg Subtype.val h), by
      rintro ⟨f, w, rfl⟩
      obtain ⟨c, hc⟩ := coordinateFunctionalTranslate_signed n w
      exact ⟨c, Subtype.ext hc.symm⟩⟩

theorem coordinateFunctionalOrbit_card (n : ℕ) :
    Nat.card (CoordinateFunctionalOrbit n) = 2 * (n + 3) := by
  rw [← Nat.card_congr (signedCoordinateOrbitEquiv n)]
  simp [mul_comm]

end Atlas.Chevalley.ClassicalDParabolic
