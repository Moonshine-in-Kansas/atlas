import Atlas.LinearGroups.Chevalley.TwistedE6.PositiveRootOrbits
import Atlas.FieldTheory.FiniteQuadraticExtension
import Mathlib.SetTheory.Cardinal.Finite

/-! Coordinate functions compatible with the explicit positive-root diagram
and quadratic conjugation. This is a set equivalence of parameter spaces only;
no root subgroup, positive group, or group isomorphism is involved.

Verification receipts are recorded separately. -/
noncomputable section

namespace Atlas.Chevalley.TwistedE6.PositiveDiagramParameters

abbrev FixedLabel := {i : Fin 36 // positiveDiagram i = i}
abbrev PairLabel := {i : Fin 36 // i < positiveDiagram i}

/-- One base-field coordinate per fixed label and one extension-field
coordinate per exchanged pair, represented by its smaller label. -/
abbrev Parameters (F K : Type*) := (FixedLabel → F) × (PairLabel → K)

theorem card_fixedLabel : Nat.card FixedLabel = 12 := by
  rw [Nat.card_eq_fintype_card]
  exact positiveDiagram_fixed_count

theorem card_pairLabel : Nat.card PairLabel = 12 := by
  rw [Nat.card_eq_fintype_card]
  exact positiveDiagram_pair_count

variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

/-- The literal subtype requested: its condition couples the two coordinates
in each diagram orbit. The degree-two hypothesis is needed for the equivalence,
not for defining this subtype. -/
def FixedFunctions :=
  {f : Fin 36 → K //
    ∀ i, f (positiveDiagram i) = Atlas.FiniteQuadratic.conjugation F K (f i)}

/-- Expand orbit parameters to all 36 coordinates. At the larger member of
an exchanged pair use the conjugate of its smaller member's parameter. -/
def expand (p : Parameters F K) (i : Fin 36) : K :=
  if hfix : positiveDiagram i = i then
    algebraMap F K (p.1 ⟨i, hfix⟩)
  else if hlt : i < positiveDiagram i then
    p.2 ⟨i, hlt⟩
  else
    Atlas.FiniteQuadratic.conjugation F K
      (p.2 ⟨positiveDiagram i, by
        rw [positiveDiagram_involutive]
        exact lt_of_le_of_ne (le_of_not_gt hlt) hfix⟩)

theorem expand_fixed (p : Parameters F K) (i : FixedLabel) :
    expand F K p i.val = algebraMap F K (p.1 i) := by
  rw [expand, dif_pos i.property]

theorem expand_pair (p : Parameters F K) (i : PairLabel) :
    expand F K p i.val = p.2 i := by
  have hfix : positiveDiagram i.val ≠ i.val := ne_of_gt i.property
  rw [expand, dif_neg hfix, dif_pos i.property]

theorem expand_partner (p : Parameters F K) (i : PairLabel) :
    expand F K p (positiveDiagram i.val) =
      Atlas.FiniteQuadratic.conjugation F K (p.2 i) := by
  have hfix : positiveDiagram (positiveDiagram i.val) ≠ positiveDiagram i.val := by
    rw [positiveDiagram_involutive]
    exact ne_of_lt i.property
  have hlt : ¬ positiveDiagram i.val < positiveDiagram (positiveDiagram i.val) := by
    rw [positiveDiagram_involutive]
    exact not_lt_of_ge (le_of_lt i.property)
  rw [expand, dif_neg hfix, dif_neg hlt]
  apply congrArg (fun j : PairLabel => Atlas.FiniteQuadratic.conjugation F K (p.2 j))
  exact Subtype.ext (positiveDiagram_involutive i.val)

theorem expand_compatible (hdeg : Module.finrank F K = 2)
    (p : Parameters F K) (i : Fin 36) :
    expand F K p (positiveDiagram i) =
      Atlas.FiniteQuadratic.conjugation F K (expand F K p i) := by
  by_cases hfix : positiveDiagram i = i
  · calc
      expand F K p (positiveDiagram i) = expand F K p i :=
        congrArg (expand F K p) hfix
      _ = algebraMap F K (p.1 ⟨i, hfix⟩) := expand_fixed F K p ⟨i, hfix⟩
      _ = Atlas.FiniteQuadratic.conjugation F K
          (algebraMap F K (p.1 ⟨i, hfix⟩)) :=
        (Atlas.FiniteQuadratic.conjugation_base F K (p.1 ⟨i, hfix⟩)).symm
      _ = Atlas.FiniteQuadratic.conjugation F K (expand F K p i) :=
        congrArg (Atlas.FiniteQuadratic.conjugation F K)
          (expand_fixed F K p ⟨i, hfix⟩).symm
  · by_cases hlt : i < positiveDiagram i
    · rw [expand_partner F K p ⟨i, hlt⟩, expand_pair F K p ⟨i, hlt⟩]
    · have hgt : positiveDiagram i < i := lt_of_le_of_ne (le_of_not_gt hlt) hfix
      let j : PairLabel := ⟨positiveDiagram i, by
        rw [positiveDiagram_involutive]
        exact hgt⟩
      have hj : positiveDiagram j.val = i := positiveDiagram_involutive i
      calc
        expand F K p (positiveDiagram i) = p.2 j := expand_pair F K p j
        _ = Atlas.FiniteQuadratic.conjugation F K
            (Atlas.FiniteQuadratic.conjugation F K (p.2 j)) :=
          (Atlas.FiniteQuadratic.conjugation_conjugation hdeg (p.2 j)).symm
        _ = Atlas.FiniteQuadratic.conjugation F K (expand F K p i) := by
          rw [← hj, expand_partner F K p j]

/-- The expansion, with its compatibility proof retained. -/
def assemble (hdeg : Module.finrank F K = 2) (p : Parameters F K) :
    FixedFunctions F K :=
  ⟨expand F K p, expand_compatible F K hdeg p⟩

@[simp] theorem assemble_val (hdeg : Module.finrank F K = 2)
    (p : Parameters F K) (i : Fin 36) :
    (assemble F K hdeg p).val i = expand F K p i := rfl

/-- A fixed diagram coordinate has a value in the actual embedded base field. -/
theorem fixedValue_exists (hdeg : Module.finrank F K = 2)
    (f : FixedFunctions F K) (i : FixedLabel) :
    ∃ a : F, algebraMap F K a = f.val i.val := by
  apply (Atlas.FiniteQuadratic.conjugation_fixed_iff hdeg (f.val i.val)).mp
  have h := f.property i.val
  rw [i.property] at h
  exact h.symm

/-- Restrict to the smaller member of each pair; at a fixed label recover
the unique base-field preimage. Choice is used only to select that preimage. -/
def extract (hdeg : Module.finrank F K = 2) (f : FixedFunctions F K) :
    Parameters F K :=
  (fun i => Classical.choose (fixedValue_exists F K hdeg f i), fun i => f.val i.val)

theorem extract_fixed_val (hdeg : Module.finrank F K = 2)
    (f : FixedFunctions F K) (i : FixedLabel) :
    algebraMap F K ((extract F K hdeg f).1 i) = f.val i.val :=
  Classical.choose_spec (fixedValue_exists F K hdeg f i)

@[simp] theorem extract_pair_val (hdeg : Module.finrank F K = 2)
    (f : FixedFunctions F K) (i : PairLabel) :
    (extract F K hdeg f).2 i = f.val i.val := rfl

theorem assemble_extract (hdeg : Module.finrank F K = 2)
    (f : FixedFunctions F K) :
    assemble F K hdeg (extract F K hdeg f) = f := by
  apply Subtype.ext
  funext i
  change expand F K (extract F K hdeg f) i = f.val i
  by_cases hfix : positiveDiagram i = i
  · exact (expand_fixed F K (extract F K hdeg f) ⟨i, hfix⟩).trans
      (extract_fixed_val F K hdeg f ⟨i, hfix⟩)
  · by_cases hlt : i < positiveDiagram i
    · exact expand_pair F K (extract F K hdeg f) ⟨i, hlt⟩
    · have hgt : positiveDiagram i < i := lt_of_le_of_ne (le_of_not_gt hlt) hfix
      let j : PairLabel := ⟨positiveDiagram i, by
        rw [positiveDiagram_involutive]
        exact hgt⟩
      have hj : positiveDiagram j.val = i := positiveDiagram_involutive i
      calc
        expand F K (extract F K hdeg f) i =
            expand F K (extract F K hdeg f) (positiveDiagram j.val) :=
          congrArg (expand F K (extract F K hdeg f)) hj.symm
        _ = Atlas.FiniteQuadratic.conjugation F K ((extract F K hdeg f).2 j) :=
          expand_partner F K (extract F K hdeg f) j
        _ = Atlas.FiniteQuadratic.conjugation F K (f.val j.val) := rfl
        _ = f.val (positiveDiagram j.val) := (f.property j.val).symm
        _ = f.val i := congrArg f.val hj

theorem extract_assemble (hdeg : Module.finrank F K = 2)
    (p : Parameters F K) :
    extract F K hdeg (assemble F K hdeg p) = p := by
  apply Prod.ext
  · funext i
    apply (algebraMap F K).injective
    calc
      algebraMap F K ((extract F K hdeg (assemble F K hdeg p)).1 i) =
          (assemble F K hdeg p).val i.val :=
        extract_fixed_val F K hdeg (assemble F K hdeg p) i
      _ = algebraMap F K (p.1 i) := expand_fixed F K p i
  · funext i
    change expand F K p i.val = p.2 i
    exact expand_pair F K p i

/-- A set equivalence, with explicit reconstruction on every diagram orbit.
This makes no assertion about the positive subgroup of a Chevalley group. -/
def fixedFunctionsEquiv (hdeg : Module.finrank F K = 2) :
    FixedFunctions F K ≃ Parameters F K where
  toFun := extract F K hdeg
  invFun := assemble F K hdeg
  left_inv := assemble_extract F K hdeg
  right_inv := extract_assemble F K hdeg

@[simp] theorem fixedFunctionsEquiv_apply_pair (hdeg : Module.finrank F K = 2)
    (f : FixedFunctions F K) (i : PairLabel) :
    (fixedFunctionsEquiv F K hdeg f).2 i = f.val i.val := rfl

theorem fixedFunctionsEquiv_apply_fixed (hdeg : Module.finrank F K = 2)
    (f : FixedFunctions F K) (i : FixedLabel) :
    algebraMap F K ((fixedFunctionsEquiv F K hdeg f).1 i) = f.val i.val :=
  extract_fixed_val F K hdeg f i

@[simp] theorem fixedFunctionsEquiv_symm_val (hdeg : Module.finrank F K = 2)
    (p : Parameters F K) (i : Fin 36) :
    ((fixedFunctionsEquiv F K hdeg).symm p).val i = expand F K p i := rfl

theorem parameters_card :
    Nat.card (Parameters F K) = Nat.card F ^ 12 * Nat.card K ^ 12 := by
  change Nat.card ((FixedLabel → F) × (PairLabel → K)) = _
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, card_fixedLabel, card_pairLabel]

/-- Count of compatible parameter functions only. No group order is claimed. -/
theorem fixedFunctions_card (hdeg : Module.finrank F K = 2) :
    Nat.card (FixedFunctions F K) = Nat.card F ^ 36 := by
  calc
    Nat.card (FixedFunctions F K) = Nat.card (Parameters F K) :=
      Nat.card_congr (fixedFunctionsEquiv F K hdeg)
    _ = Nat.card F ^ 12 * Nat.card K ^ 12 := parameters_card F K
    _ = Nat.card F ^ 12 * (Nat.card F ^ 2) ^ 12 := by
      rw [Atlas.FiniteQuadratic.card_extension hdeg]
    _ = Nat.card F ^ (12 + 2 * 12) := by rw [pow_add, pow_mul]
    _ = Nat.card F ^ 36 := rfl

end Atlas.Chevalley.TwistedE6.PositiveDiagramParameters
