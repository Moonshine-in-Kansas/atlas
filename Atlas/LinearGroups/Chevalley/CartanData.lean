/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the repository license; see LICENSE.
-/
import Atlas.LinearGroups.Chevalley.RootType
import Mathlib.LinearAlgebra.Matrix.Cartan

/-! # The pinned Cartan matrices of all nine untwisted types

This adapter uses mathlib's node numbering, including E6, E7 and E8. It does not
assert existence of a root pairing with these matrices: that realization, including
its root and weight lattices, remains a separate construction obligation.
-/

namespace Atlas.Chevalley.RootType

/-- The actual integer Cartan matrix in the pinned mathlib numbering. -/
def cartan (Φ : RootType) : Matrix (Fin Φ.rank) (Fin Φ.rank) ℤ :=
  match Φ with
  | A r _ => CartanMatrix.A r
  | B r _ => CartanMatrix.B r
  | C r _ => CartanMatrix.C r
  | D r _ => CartanMatrix.D r
  | E6 => CartanMatrix.E 6
  | E7 => CartanMatrix.E 7
  | E8 => CartanMatrix.E 8
  | F4 => CartanMatrix.F₄
  | G2 => CartanMatrix.G₂

@[simp] theorem cartan_diag (Φ : RootType) (i : Fin Φ.rank) : Φ.cartan i i = 2 := by
  cases Φ with
  | A r _ => exact congrFun (CartanMatrix.A_diag r) i
  | B r _ => exact CartanMatrix.B_diag r i
  | C r _ => exact CartanMatrix.C_diag r i
  | D r _ => exact CartanMatrix.D_diag r i
  | E6 => exact CartanMatrix.E_diag 6 i
  | E7 => exact CartanMatrix.E_diag 7 i
  | E8 => exact CartanMatrix.E_diag 8 i
  | F4 => exact CartanMatrix.F₄_diag i
  | G2 => exact CartanMatrix.G₂_diag i

theorem cartan_off_diag_nonpos (Φ : RootType) (i j : Fin Φ.rank) (h : i ≠ j) :
    Φ.cartan i j ≤ 0 := by
  cases Φ with
  | A r _ => exact CartanMatrix.A_apply_le_zero_of_ne r i j h
  | B r _ => exact CartanMatrix.B_off_diag_nonpos r i j h
  | C r _ => exact CartanMatrix.C_off_diag_nonpos r i j h
  | D r _ => exact CartanMatrix.D_off_diag_nonpos r i j h
  | E6 => exact CartanMatrix.E_off_diag_nonpos 6 i j h
  | E7 => exact CartanMatrix.E_off_diag_nonpos 7 i j h
  | E8 => exact CartanMatrix.E_off_diag_nonpos 8 i j h
  | F4 => exact CartanMatrix.F₄_off_diag_nonpos i j h
  | G2 => exact CartanMatrix.G₂_off_diag_nonpos i j h

/-- Dual root labels exchange the two directed double-edge matrices. -/
theorem cartan_B_transpose (r : ℕ) (h : 2 ≤ r) :
    (B r h).cartan.transpose = (C r h).cartan := CartanMatrix.B_transpose r

/-- The directed edges are retained rather than forgetting the B/C distinction. -/
theorem cartan_B2_ne_C2 : (B 2 (by decide)).cartan ≠ (C 2 (by decide)).cartan := by
  intro h
  change CartanMatrix.B 2 = CartanMatrix.C 2 at h
  have h01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 1) h
  change (-2 : ℤ) = -1 at h01
  omega

/-- Exceptional matrices are concrete data, not deferred family labels. -/
theorem cartan_E6_explicit : E6.cartan = CartanMatrix.E 6 := rfl

theorem cartan_E7_explicit : E7.cartan = CartanMatrix.E 7 := rfl

theorem cartan_E8_explicit : E8.cartan = CartanMatrix.E 8 := rfl

end Atlas.Chevalley.RootType
