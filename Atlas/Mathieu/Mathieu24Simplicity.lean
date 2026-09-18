/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSE.
Authors: ATLAS contributors
-/
import Atlas.Mathieu.Mathieu23Simplicity
import Atlas.GroupTheory.SimpleStabilizer

/-! Nonabelian simplicity of the existing full coordinate automorphism group of Golay. -/

namespace Atlas.Codes

theorem mathieu24_simple : IsSimpleGroup Mathieu24CodeModel := by
  let a : Omega := ((0, 0), 0)
  have := mathieu24_five_transitive
  have : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 5)
      (by norm_num [Omega, HexIndex])
  have : IsSimpleGroup (MulAction.stabilizer Mathieu24CodeModel a) := mathieu23_simple a
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact Atlas.GroupTheory.simple_of_simple_stabilizer (G := Mathieu24CodeModel)
    (X := Omega) a 2 3 (by decide) (by norm_num [Omega, HexIndex])
    (by norm_num [Omega, HexIndex])

theorem mathieu24_nonabelian_simple : IsSimpleGroup Mathieu24CodeModel ∧
    ∃ g h : Mathieu24CodeModel, g * h ≠ h * g :=
  ⟨mathieu24_simple, mathieu24_noncommuting_pair⟩

end Atlas.Codes
