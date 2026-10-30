import F4Work.SplitKernelSemidirect
import F4Work.MarkedLineStabilizerRestriction

/-!
Source-only, uncompiled. The actual full marked-line stabilizer splits as
its literal pointwise kernel semidirect the existing concrete GL2 section.
This structural module uses neither kernel recognition nor any group order.
Root filtration, Borel/intersection and residues are separate obligations.
-/

noncomputable section
namespace Atlas.ReeF4
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Actual GL2 conjugation on the full pointwise-line kernel. -/
def markedLineKernelGL2Action {m : ℕ} (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    Matrix.GeneralLinearGroup (Fin 2) F →* MulAut (markedLineRestrictionKernel (F := F) m) :=
  Atlas.GroupTheory.splitKernelAction (markedLineRestriction m) (markedLineLeviSection hcard)

theorem markedLineKernelGL2Action_apply {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (B : Matrix.GeneralLinearGroup (Fin 2) F) (k : markedLineRestrictionKernel (F := F) m) :
    (markedLineKernelGL2Action hcard B k).val.val =
      modelLongGL2Hom hcard B * k.val.val * (modelLongGL2Hom hcard B)⁻¹ := rfl

/-- The full line parabolic, via its actual restriction and literal splitting section. -/
def lineParabolicSemidirectEquiv {m : ℕ} (hcard : Nat.card F = 2 ^ (2 * m + 1)) :
    markedLineRestrictionKernel (F := F) m ⋊[markedLineKernelGL2Action hcard]
      Matrix.GeneralLinearGroup (Fin 2) F ≃* markedLineStabilizer (F := F) m :=
  Atlas.GroupTheory.splitKernelMulEquiv (markedLineRestriction m)
    (markedLineLeviSection hcard) (markedLineRestriction_section hcard)

theorem lineParabolicSemidirectEquiv_apply {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (x : markedLineRestrictionKernel (F := F) m ⋊[markedLineKernelGL2Action hcard]
      Matrix.GeneralLinearGroup (Fin 2) F) :
    lineParabolicSemidirectEquiv hcard x = x.left.val * markedLineLeviSection hcard x.right := rfl

/-- The same intrinsic Model operator is the ordered product of kernel and embedded GL2. -/
theorem lineParabolicSemidirectEquiv_val {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (x : markedLineRestrictionKernel (F := F) m ⋊[markedLineKernelGL2Action hcard]
      Matrix.GeneralLinearGroup (Fin 2) F) :
    (lineParabolicSemidirectEquiv hcard x).val =
      x.left.val.val * modelLongGL2Hom hcard x.right := rfl

theorem lineParabolicSemidirectEquiv_inl {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (k : markedLineRestrictionKernel (F := F) m) :
    lineParabolicSemidirectEquiv hcard (SemidirectProduct.inl k) = k.val :=
  Atlas.GroupTheory.splitKernelMulEquiv_inl (markedLineRestriction m)
    (markedLineLeviSection hcard) (markedLineRestriction_section hcard) k

theorem lineParabolicSemidirectEquiv_inr {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    lineParabolicSemidirectEquiv hcard (SemidirectProduct.inr B) = markedLineLeviSection hcard B :=
  Atlas.GroupTheory.splitKernelMulEquiv_inr (markedLineRestriction m)
    (markedLineLeviSection hcard) (markedLineRestriction_section hcard) B

theorem lineParabolicSemidirectEquiv_restriction {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1))
    (x : markedLineRestrictionKernel (F := F) m ⋊[markedLineKernelGL2Action hcard]
      Matrix.GeneralLinearGroup (Fin 2) F) :
    markedLineRestriction m (lineParabolicSemidirectEquiv hcard x) = x.right :=
  Atlas.GroupTheory.splitKernelMulEquiv_right (markedLineRestriction m)
    (markedLineLeviSection hcard) (markedLineRestriction_section hcard) x

theorem lineParabolicSemidirectEquiv_symm_right {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : markedLineStabilizer (F := F) m) :
    ((lineParabolicSemidirectEquiv hcard).symm g).right = markedLineRestriction m g :=
  Atlas.GroupTheory.splitKernelMulEquiv_symm_right (markedLineRestriction m)
    (markedLineLeviSection hcard) (markedLineRestriction_section hcard) g

theorem lineParabolicSemidirectEquiv_symm_left {m : ℕ}
    (hcard : Nat.card F = 2 ^ (2 * m + 1)) (g : markedLineStabilizer (F := F) m) :
    ((lineParabolicSemidirectEquiv hcard).symm g).left.val =
      g * (markedLineLeviSection hcard (markedLineRestriction m g))⁻¹ :=
  Atlas.GroupTheory.splitKernelMulEquiv_symm_left (markedLineRestriction m)
    (markedLineLeviSection hcard) (markedLineRestriction_section hcard) g

end Atlas.ReeF4
