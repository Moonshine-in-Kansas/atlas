import Atlas.Comparisons.CatalogueOrders

/-! Typed catalogue of the completed ATLAS constructions. Numerical labels are
metadata: the carrier below is always the retained concrete group, never a group
chosen by order or by an existence theorem. Low-rank duplicate presentations outside
the arithmetic label ranges remain available in the separate comparison interfaces. -/
noncomputable section
namespace Atlas.Comparisons.Catalogue
open Atlas.OrderArithmetic

/-- A concrete finite field, with no choice of a canonical representation. -/
structure FiniteField where
  carrier : Type
  [field : Field carrier]
  [finite : Finite carrier]
attribute [instance] FiniteField.field FiniteField.finite

/-- An actual finite field extension with its specified degree. -/
structure Extension (degree : ℕ) where
  base : FiniteField
  extension : FiniteField
  [algebra : Algebra base.carrier extension.carrier]
  finrank : Module.finrank base.carrier extension.carrier = degree
attribute [instance] Extension.algebra

/-- A concrete finite field with its characteristic instance recorded. -/
structure FieldOfChar (p : ℕ) where
  field : FiniteField
  [charP : CharP field.carrier p]
attribute [instance] FieldOfChar.charP

/-- Only fixed groups with completed actual constructions enter this registry. -/
inductive Fixed
  | M11 | M12 | M22 | M23 | M24 | Co1 | Co2 | Co3 | McL | HS | Suz | J2
  | Fi22 | Fi23 | Fi24prime | Ru | Tits
  deriving DecidableEq, Repr

def Fixed.label : Fixed → FixedLabel
  | .M11 => .M11 | .M12 => .M12 | .M22 => .M22 | .M23 => .M23 | .M24 => .M24
  | .Co1 => .Co1 | .Co2 => .Co2 | .Co3 => .Co3 | .McL => .McL | .HS => .HS
  | .Suz => .Suz | .J2 => .J2 | .Fi22 => .Fi22 | .Fi23 => .Fi23
  | .Fi24prime => .Fi24prime | .Ru => .Ru | .Tits => .Tits

def Fixed.Model : Fixed → Type
  | .M11 => Atlas.Sporadic.Mathieu11.StandardModel
  | .M12 => Atlas.Sporadic.Mathieu12.StandardModel
  | .M22 => Atlas.Sporadic.Mathieu22.Model ((0,0),0)
      ⟨((0,0),1), by change ((0,0),1) ≠ ((0,0),0); decide⟩
  | .M23 => Atlas.Sporadic.Mathieu23.Model ((0,0),0)
  | .M24 => Atlas.Sporadic.Mathieu24.Model
  | .Co1 => Atlas.Sporadic.Conway1.Model
  | .Co2 => Atlas.Sporadic.Conway2.Model
  | .Co3 => Atlas.Sporadic.Conway3.Model
  | .McL => Atlas.Sporadic.McLaughlin.Model
  | .HS => Atlas.Sporadic.HigmanSims.Model
  | .Suz => Atlas.Sporadic.Suzuki.Model
  | .J2 => Atlas.Sporadic.Janko2.Model
  | .Fi22 => Atlas.Sporadic.Fischer22.Model
  | .Fi23 => Atlas.Sporadic.Fischer23.Model
  | .Fi24prime => Atlas.Sporadic.Fischer24Prime.Model
  | .Ru => Atlas.Sporadic.Rudvalis.Model
  | .Tits => Atlas.Tits.Model

instance Fixed.modelGroup (x : Fixed) : Group x.Model := by
  cases x <;> dsimp [Fixed.Model] <;> infer_instance

/-- The exact simple parameter ranges are retained as arithmetic admissibility
proofs. Extension and characteristic witnesses affect the actual carrier. -/
inductive Entry
  | cyclic (p : ℕ) (hp : p.Prime)
  | alternating (n : ℕ) (hn : 5 ≤ n)
  | linear (F : FiniteField) (d : ℕ)
      (h : Admissible (.linear d (Nat.card F.carrier)))
  | unitary (E : Extension 2) (d : ℕ)
      (h : Admissible (.unitary d (Nat.card E.base.carrier)))
  | B (F : FiniteField) (r : ℕ) (h : Admissible (.B r (Nat.card F.carrier)))
  | C (F : FiniteField) (r : ℕ) (h : Admissible (.C r (Nat.card F.carrier)))
  | Dplus (F : FiniteField) (r : ℕ)
      (h : Admissible (.Dplus r (Nat.card F.carrier)))
  | Dminus (E : Extension 2) (r : ℕ)
      (h : Admissible (.Dminus r (Nat.card E.base.carrier)))
  | G2 (F : FiniteField) (h : Admissible (.G2 (Nat.card F.carrier)))
  | F4 (F : FiniteField) (h : Admissible (.F4 (Nat.card F.carrier)))
  | triality (E : Extension 3)
      (h : Admissible (.trialityD4 (Nat.card E.base.carrier)))
  | suzuki (F : FieldOfChar 2) (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card F.field.carrier = 2 ^ (2 * m + 1))
  | smallRee (F : FieldOfChar 3) (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card F.field.carrier = 3 ^ (2 * m + 1))
  | fixed (x : Fixed)

def label : Entry → RawEntry
  | .cyclic p _ => .cyclic p
  | .alternating n _ => .alternating n
  | .linear F d _ => .linear d (Nat.card F.carrier)
  | .unitary E d _ => .unitary d (Nat.card E.base.carrier)
  | .B F r _ => .B r (Nat.card F.carrier)
  | .C F r _ => .C r (Nat.card F.carrier)
  | .Dplus F r _ => .Dplus r (Nat.card F.carrier)
  | .Dminus E r _ => .Dminus r (Nat.card E.base.carrier)
  | .G2 F _ => .G2 (Nat.card F.carrier)
  | .F4 F _ => .F4 (Nat.card F.carrier)
  | .triality E _ => .trialityD4 (Nat.card E.base.carrier)
  | .suzuki F _ _ _ => .suzuki (Nat.card F.field.carrier)
  | .smallRee F _ _ _ => .smallRee (Nat.card F.field.carrier)
  | .fixed x => .fixed x.label

/-- The exact original group attached to a catalogue entry. -/
def Model : Entry → Type
  | .cyclic p _ => Atlas.Families.Cyclic.Model p
  | .alternating n _ => Atlas.Families.Alternating.Model n
  | .linear F d _ => Matrix.ProjectiveSpecialLinearGroup (Fin d) F.carrier
  | .unitary E d _ => Atlas.Unitary.PSU E.base.carrier E.extension.carrier d E.finrank
  | .B F r _ => Atlas.Orthogonal.B r F.carrier
  | .C F r _ => Atlas.Symplectic.PSp r F.carrier
  | .Dplus F r _ => Atlas.Orthogonal.DPlus r F.carrier
  | .Dminus E r _ => Atlas.Orthogonal.DMinus r E.base.carrier E.extension.carrier E.finrank
  | .G2 F _ => Atlas.G2.Model F.carrier
  | .F4 F _ => Atlas.F4.Model F.carrier
  | .triality E _ => Atlas.Triality.Group E.base.carrier E.extension.carrier
  | .suzuki F m _ _ => Atlas.SuzukiFamily.Group F.field.carrier m
  | .smallRee F m _ _ => Atlas.ReeG2.Model F.field.carrier m
  | .fixed x => x.Model

instance modelGroup (x : Entry) : Group (Model x) := by
  cases x <;> dsimp [Model] <;> infer_instance

/-- No planned or nonsimple parameter enters the typed registry. -/
theorem admissible (x : Entry) : Admissible (label x) := by
  cases x with
  | cyclic p hp => exact hp
  | alternating n hn => exact hn
  | linear F d h => exact h
  | unitary E d h => exact h
  | B F r h => exact h
  | C F r h => exact h
  | Dplus F r h => exact h
  | Dminus E r h => exact h
  | G2 F h => exact h
  | F4 F h => exact h
  | triality E h => exact h
  | suzuki F m hm hcard => exact ⟨m, hm, hcard⟩
  | smallRee F m hm hcard => exact ⟨m, hm, hcard⟩
  | fixed x => trivial

end Atlas.Comparisons.Catalogue
