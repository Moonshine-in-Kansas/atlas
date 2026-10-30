import Atlas.LinearGroups.Chevalley.TwistedE6.TorusAnchors
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
Verification receipts are recorded separately.

Public simple-coroot coordinates for the actual selected E6 torus, whole-tuple
graph/Frobenius covariance, and the exact fixed-tuple criterion. This module
stops at the tuple equations; it does not solve or count their solutions.

The graph formula uses the public `simpleNode` permutation, without inversion
of a unit parameter. The fixed criterion itself needs no degree-two premise.
-/

noncomputable section

namespace Atlas.Chevalley.TwistedE6

open Classical

section Torus

variable (K : Type*) [Field K]

/-- Reindex public simple-coroot parameters by the inherited actual base support. -/
def e6PublicTorusReindex :
    (Fin 6 → Kˣ) ≃* ((rootDatum .E6).base.support → Kˣ) where
  toFun t j := t ((rootDatum .E6).indexEquiv.symm j)
  invFun t i := t ((rootDatum .E6).indexEquiv i)
  left_inv t := by
    funext i
    exact congrArg t ((rootDatum .E6).indexEquiv.symm_apply_apply i)
  right_inv t := by
    funext j
    exact congrArg t ((rootDatum .E6).indexEquiv.apply_symm_apply j)
  map_mul' _ _ := rfl

@[simp] theorem e6PublicTorusReindex_apply (t : Fin 6 → Kˣ)
    (j : (rootDatum .E6).base.support) :
    e6PublicTorusReindex K t j = t ((rootDatum .E6).indexEquiv.symm j) := rfl

@[simp] theorem e6PublicTorusReindex_mulSingle (i : Fin 6) (a : Kˣ) :
    e6PublicTorusReindex K (Pi.mulSingle i a) =
      Pi.mulSingle ((rootDatum .E6).indexEquiv i) a := by
  change (Pi.mulSingle i a : Fin 6 → Kˣ) ∘ (rootDatum .E6).indexEquiv.symm = _
  exact Pi.mulSingle_comp_equiv (rootDatum .E6).indexEquiv.symm i a

/-- The inherited actual torus parameter homomorphism, in public node order. -/
def e6PublicTorusParameters : (Fin 6 → Kˣ) →* SelectedWeightCompanion .E6 K :=
  (selectedWeightCompanionTorusParameters .E6 K).comp
    (e6PublicTorusReindex K).toMonoidHom

theorem e6PublicTorusParameters_apply (t : Fin 6 → Kˣ) :
    e6PublicTorusParameters K t =
      selectedWeightCompanionTorusParameters .E6 K
        (fun j => t ((rootDatum .E6).indexEquiv.symm j)) := rfl

/-- This equivalence lands in the existing generated torus, not an abstract copy. -/
def e6PublicTorusParametersEquiv :
    (Fin 6 → Kˣ) ≃* selectedWeightCompanionTorusSubgroup .E6 K :=
  (e6PublicTorusReindex K).trans (e6TorusParametersEquiv K)

@[simp] theorem e6PublicTorusParametersEquiv_val (t : Fin 6 → Kˣ) :
    (e6PublicTorusParametersEquiv K t : SelectedWeightCompanion .E6 K) =
      e6PublicTorusParameters K t := rfl

theorem e6PublicTorusParameters_injective :
    Function.Injective (e6PublicTorusParameters K) := by
  intro t u h
  apply (e6PublicTorusReindex K).injective
  exact selectedWeightCompanionTorusParameters_injective .E6 K h

theorem e6PublicTorusParameters_mem (t : Fin 6 → Kˣ) :
    e6PublicTorusParameters K t ∈ selectedWeightCompanionTorusSubgroup .E6 K :=
  (e6PublicTorusParametersEquiv K t).property

@[simp] theorem e6PublicTorusParameters_mulSingle (i : Fin 6) (a : Kˣ) :
    e6PublicTorusParameters K (Pi.mulSingle i a) = e6SimpleTorus K i a := by
  change selectedWeightCompanionTorusParameters .E6 K
    (e6PublicTorusReindex K (Pi.mulSingle i a)) = _
  rw [e6PublicTorusReindex_mulSingle, e6TorusParameters_single]

/-- Pull back a tuple by the public diagram involution. -/
def e6TorusTupleDiagram : (Fin 6 → Kˣ) ≃* (Fin 6 → Kˣ) where
  toFun t i := t (simpleNode i)
  invFun t i := t (simpleNode i)
  left_inv t := by
    funext i
    exact congrArg t (simpleNode_involutive i)
  right_inv t := by
    funext i
    exact congrArg t (simpleNode_involutive i)
  map_mul' _ _ := rfl

@[simp] theorem e6TorusTupleDiagram_apply (t : Fin 6 → Kˣ) (i : Fin 6) :
    e6TorusTupleDiagram K t i = t (simpleNode i) := rfl

@[simp] theorem e6TorusTupleDiagram_mulSingle (i : Fin 6) (a : Kˣ) :
    e6TorusTupleDiagram K (Pi.mulSingle i a) = Pi.mulSingle (simpleNode i) a := by
  have hi : simpleNode.symm i = simpleNode i := by
    apply simpleNode.injective
    rw [Equiv.apply_symm_apply, simpleNode_involutive]
  change (Pi.mulSingle i a : Fin 6 → Kˣ) ∘ simpleNode = _
  rw [Pi.mulSingle_comp_equiv, hi]

/-- Extend the actual simple-coroot graph action to every torus tuple. -/
theorem companionDiagram_e6PublicTorusParameters (t : Fin 6 → Kˣ) :
    companionDiagram K (e6PublicTorusParameters K t) =
      e6PublicTorusParameters K (e6TorusTupleDiagram K t) := by
  refine Pi.mulSingle_induction
    (fun t : Fin 6 → Kˣ =>
      companionDiagram K (e6PublicTorusParameters K t) =
        e6PublicTorusParameters K (e6TorusTupleDiagram K t)) t ?_ ?_ ?_
  · simp only [map_one]
  · intro t u ht hu
    simp only [map_mul, ht, hu]
  · intro i a
    rw [e6PublicTorusParameters_mulSingle, companionDiagram_e6SimpleTorus,
      e6TorusTupleDiagram_mulSingle, e6PublicTorusParameters_mulSingle]

end Torus

section Fixed

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- Coefficient Frobenius applied to each unit coordinate. -/
def e6TorusTupleFrobenius : (Fin 6 → Kˣ) ≃* (Fin 6 → Kˣ) where
  toFun t i := conjugationUnits F K (t i)
  invFun t i := (conjugationUnits F K).symm (t i)
  left_inv t := by
    funext i
    exact (conjugationUnits F K).symm_apply_apply (t i)
  right_inv t := by
    funext i
    exact (conjugationUnits F K).apply_symm_apply (t i)
  map_mul' t u := by
    funext i
    exact map_mul (conjugationUnits F K) (t i) (u i)

@[simp] theorem e6TorusTupleFrobenius_apply (t : Fin 6 → Kˣ) (i : Fin 6) :
    e6TorusTupleFrobenius F K t i = conjugationUnits F K (t i) := rfl

@[simp] theorem e6TorusTupleFrobenius_mulSingle (i : Fin 6) (a : Kˣ) :
    e6TorusTupleFrobenius F K (Pi.mulSingle i a) =
      Pi.mulSingle i (conjugationUnits F K a) := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [e6TorusTupleFrobenius_apply, Pi.mulSingle_eq_same]
  · simp only [e6TorusTupleFrobenius_apply, Pi.mulSingle_eq_of_ne h, map_one]

/-- Extend the actual simple-coroot Frobenius action to every torus tuple. -/
theorem companionFrobenius_e6PublicTorusParameters (t : Fin 6 → Kˣ) :
    companionFrobenius F K (e6PublicTorusParameters K t) =
      e6PublicTorusParameters K (e6TorusTupleFrobenius F K t) := by
  refine Pi.mulSingle_induction
    (fun t : Fin 6 → Kˣ =>
      companionFrobenius F K (e6PublicTorusParameters K t) =
        e6PublicTorusParameters K (e6TorusTupleFrobenius F K t)) t ?_ ?_ ?_
  · simp only [map_one]
  · intro t u ht hu
    simp only [map_mul, ht, hu]
  · intro i a
    rw [e6PublicTorusParameters_mulSingle, companionFrobenius_e6SimpleTorus,
      e6TorusTupleFrobenius_mulSingle, e6PublicTorusParameters_mulSingle]

/-- The combined twist acts on public tuples by i ↦ σ(t_(δ i)). -/
theorem companionTwist_e6PublicTorusParameters (t : Fin 6 → Kˣ) :
    companionTwist F K (e6PublicTorusParameters K t) =
      e6PublicTorusParameters K (fun i => conjugationUnits F K (t (simpleNode i))) := by
  change companionDiagram K (companionFrobenius F K (e6PublicTorusParameters K t)) = _
  rw [companionFrobenius_e6PublicTorusParameters]
  exact companionDiagram_e6PublicTorusParameters K (e6TorusTupleFrobenius F K t)

/-- The exact equations, using injectivity in the actual selected companion. -/
theorem e6PublicTorusParameters_mem_companionFixedSubgroup_iff (t : Fin 6 → Kˣ) :
    e6PublicTorusParameters K t ∈ companionFixedSubgroup F K ↔
      ∀ i : Fin 6, conjugationUnits F K (t i) = t (simpleNode i) := by
  rw [mem_companionFixedSubgroup_iff, companionFrobenius_e6PublicTorusParameters,
    companionDiagram_e6PublicTorusParameters]
  constructor
  · intro h i
    exact congrFun (e6PublicTorusParameters_injective K h) i
  · intro h
    apply congrArg (e6PublicTorusParameters K)
    funext i
    exact h i

/-- The same criterion for the literal fixed torus T ∩ C. -/
theorem e6PublicTorusParameters_mem_companionFixedTorus_iff (t : Fin 6 → Kˣ) :
    e6PublicTorusParameters K t ∈ companionFixedTorus F K ↔
      ∀ i : Fin 6, conjugationUnits F K (t i) = t (simpleNode i) := by
  change
    (e6PublicTorusParameters K t ∈ selectedWeightCompanionTorusSubgroup .E6 K ∧
      e6PublicTorusParameters K t ∈ companionFixedSubgroup F K) ↔ _
  constructor
  · intro h
    exact (e6PublicTorusParameters_mem_companionFixedSubgroup_iff F K t).mp h.2
  · intro h
    exact ⟨e6PublicTorusParameters_mem K t,
      (e6PublicTorusParameters_mem_companionFixedSubgroup_iff F K t).mpr h⟩

/-- The equivalence with the existing torus exposes the same fixed equations. -/
theorem e6PublicTorusParametersEquiv_mem_companionFixedSubgroup_iff (t : Fin 6 → Kˣ) :
    (e6PublicTorusParametersEquiv K t : SelectedWeightCompanion .E6 K) ∈
        companionFixedSubgroup F K ↔
      ∀ i : Fin 6, conjugationUnits F K (t i) = t (simpleNode i) := by
  rw [e6PublicTorusParametersEquiv_val]
  exact e6PublicTorusParameters_mem_companionFixedSubgroup_iff F K t

end Fixed

end Atlas.Chevalley.TwistedE6
