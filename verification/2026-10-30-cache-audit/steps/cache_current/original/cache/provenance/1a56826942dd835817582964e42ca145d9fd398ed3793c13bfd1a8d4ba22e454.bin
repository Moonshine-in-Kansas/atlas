/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.Mathieu24ConstructionPackage

/-! Public interface for the retained full Golay code automorphism group.
Simplicity and further recognition results are not part of this package. -/
namespace Atlas.Sporadic.Mathieu24

/-- The existing full permutation automorphism group of the constructed binary Golay code. -/
abbrev Model := ↥Atlas.Codes.Mathieu24CodeModel
abbrev Points := Atlas.Codes.Omega

theorem finite : Finite Model := inferInstance

theorem order : Nat.card Model = 244823040 := Atlas.Codes.mathieu24_order

theorem faithful : FaithfulSMul Model Points := inferInstance

theorem five_transitive : MulAction.IsMultiplyPretransitive Model Points 5 :=
  Atlas.Codes.mathieu24_five_transitive

theorem not_six_transitive : ¬ MulAction.IsMultiplyPretransitive Model Points 6 :=
  Atlas.Codes.mathieu24_not_six_transitive

theorem noncommuting_pair : ∃ g h : Model, g*h ≠ h*g := Atlas.Codes.mathieu24_noncommuting_pair

theorem alternating : Atlas.Codes.Mathieu24CodeModel ≤ alternatingGroup Points :=
  Atlas.Codes.mathieu24_le_alternating

theorem construction : Atlas.Codes.Mathieu24HexacodeConstructionPackage :=
  Atlas.Codes.mathieu24_hexacode_construction

end Atlas.Sporadic.Mathieu24
