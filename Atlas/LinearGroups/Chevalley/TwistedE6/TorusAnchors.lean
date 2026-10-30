import Atlas.LinearGroups.Chevalley.TwistedE6.CompanionTwist
import Atlas.LinearGroups.Chevalley.SelectedWeightCompanionTorusOrder
import Mathlib.Algebra.Group.Units.Equiv

/-!
Verification receipts are recorded separately.

Actual selected E6 torus interfaces and the action on its simple-coroot words.
The full fixed-parameter equivalence and cardinality are not declared here.
-/

noncomputable section

namespace Atlas.Chevalley.TwistedE6

open Classical

section Torus

variable (K : Type*) [Field K]

/-- Specialize the inherited equivalence with the actual generated torus. -/
def e6TorusParametersEquiv :
    ((rootDatum .E6).base.support → Kˣ) ≃*
      selectedWeightCompanionTorusSubgroup .E6 K :=
  weightCompanionTorusParametersEquiv (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K (selectedWeightSet_spans .E6)

theorem e6TorusSubgroup_eq_range :
    selectedWeightCompanionTorusSubgroup .E6 K =
      (selectedWeightCompanionTorusParameters .E6 K).range :=
  weightCompanionTorusSubgroup_eq_range (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K

/-- The inherited Weyl word, with a unit parameter and public simple-node label. -/
def e6SimpleWeylUnit (i : Fin 6) (a : Kˣ) : SelectedWeightCompanion .E6 K :=
  selectedWeightCompanionX .E6 K i a.val *
    selectedWeightCompanionY .E6 K i (-a.inv) *
      selectedWeightCompanionX .E6 K i a.val

def e6SimpleTorus (i : Fin 6) (a : Kˣ) : SelectedWeightCompanion .E6 K :=
  e6SimpleWeylUnit K i a * (e6SimpleWeylUnit K i 1)⁻¹

/-- The new notation is literally the existing simple-coroot torus word. -/
theorem e6SimpleTorus_eq_inherited (i : Fin 6) (a : Kˣ) :
    e6SimpleTorus K i a =
      weightCompanionTorus (rootDatum .E6).pairing (rootDatum .E6).base
        (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
        (selectedWeightOrbits_minuscule .E6) K ((rootDatum .E6).indexEquiv i) a := rfl

theorem e6TorusParameters_single (i : Fin 6) (a : Kˣ) :
    selectedWeightCompanionTorusParameters .E6 K
        (Pi.mulSingle ((rootDatum .E6).indexEquiv i) a) = e6SimpleTorus K i a :=
  weightCompanionTorusParameters_single (rootDatum .E6).pairing (rootDatum .E6).base
    (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
    (selectedWeightOrbits_minuscule .E6) K ((rootDatum .E6).indexEquiv i) a

theorem companionDiagram_e6SimpleWeylUnit (i : Fin 6) (a : Kˣ) :
    companionDiagram K (e6SimpleWeylUnit K i a) =
      e6SimpleWeylUnit K (simpleNode i) a := by
  simp only [e6SimpleWeylUnit, map_mul, companionDiagram_X, companionDiagram_Y]

/-- The graph acts by the simple-node permutation, without inversion of the unit. -/
theorem companionDiagram_e6SimpleTorus (i : Fin 6) (a : Kˣ) :
    companionDiagram K (e6SimpleTorus K i a) = e6SimpleTorus K (simpleNode i) a := by
  simp only [e6SimpleTorus, map_mul, map_inv, companionDiagram_e6SimpleWeylUnit]

end Torus

section Fixed

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Conjugation on the actual extension units; no norm-one restriction. -/
def conjugationUnits : Kˣ ≃* Kˣ :=
  Units.mapEquiv (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv.toMulEquiv

theorem companionFrobenius_e6SimpleWeylUnit (i : Fin 6) (a : Kˣ) :
    companionFrobenius F K (e6SimpleWeylUnit K i a) =
      e6SimpleWeylUnit K i (conjugationUnits F K a) := by
  have hx (t : K) :
      companionFrobenius F K (selectedWeightCompanionX .E6 K i t) =
        selectedWeightCompanionX .E6 K i (Atlas.FiniteQuadratic.conjugation F K t) :=
    weightCompanionEquiv_X (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6)
      (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv ((rootDatum .E6).indexEquiv i) t
  have hy (t : K) :
      companionFrobenius F K (selectedWeightCompanionY .E6 K i t) =
        selectedWeightCompanionY .E6 K i (Atlas.FiniteQuadratic.conjugation F K t) :=
    weightCompanionEquiv_Y (rootDatum .E6).pairing (rootDatum .E6).base
      (selectedWeightOrbits .E6) (selectedWeightOrbits_closed .E6)
      (selectedWeightOrbits_minuscule .E6)
      (Atlas.FiniteQuadratic.conjugation F K).toRingEquiv ((rootDatum .E6).indexEquiv i) t
  simp only [e6SimpleWeylUnit, map_mul, hx, hy]
  change
    selectedWeightCompanionX .E6 K i (Atlas.FiniteQuadratic.conjugation F K a.val) *
      selectedWeightCompanionY .E6 K i (Atlas.FiniteQuadratic.conjugation F K (-a.inv)) *
        selectedWeightCompanionX .E6 K i (Atlas.FiniteQuadratic.conjugation F K a.val) =
    selectedWeightCompanionX .E6 K i (Atlas.FiniteQuadratic.conjugation F K a.val) *
      selectedWeightCompanionY .E6 K i (-(Atlas.FiniteQuadratic.conjugation F K a.inv)) *
        selectedWeightCompanionX .E6 K i (Atlas.FiniteQuadratic.conjugation F K a.val)
  rw [map_neg]

theorem companionFrobenius_e6SimpleTorus (i : Fin 6) (a : Kˣ) :
    companionFrobenius F K (e6SimpleTorus K i a) =
      e6SimpleTorus K i (conjugationUnits F K a) := by
  simp only [e6SimpleTorus, map_mul, map_inv, companionFrobenius_e6SimpleWeylUnit, map_one]

theorem companionTwist_e6SimpleTorus (i : Fin 6) (a : Kˣ) :
    companionTwist F K (e6SimpleTorus K i a) =
      e6SimpleTorus K (simpleNode i) (conjugationUnits F K a) := by
  change companionDiagram K (companionFrobenius F K (e6SimpleTorus K i a)) = _
  rw [companionFrobenius_e6SimpleTorus, companionDiagram_e6SimpleTorus]

/-- The desired subgroup is the literal intersection in the selected companion. -/
def companionFixedTorus : Subgroup (SelectedWeightCompanion .E6 K) :=
  selectedWeightCompanionTorusSubgroup .E6 K ⊓ companionFixedSubgroup F K

theorem mem_companionFixedTorus_iff (g : SelectedWeightCompanion .E6 K) :
    g ∈ companionFixedTorus F K ↔
      g ∈ selectedWeightCompanionTorusSubgroup .E6 K ∧
        companionFrobenius F K g = companionDiagram K g := by
  change (g ∈ selectedWeightCompanionTorusSubgroup .E6 K ∧
    g ∈ companionFixedSubgroup F K) ↔ _
  rw [mem_companionFixedSubgroup_iff]

end Fixed

end Atlas.Chevalley.TwistedE6
