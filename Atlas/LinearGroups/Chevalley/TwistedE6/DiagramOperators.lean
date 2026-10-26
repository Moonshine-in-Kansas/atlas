import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramStrings
import Atlas.LinearGroups.Chevalley.Integral.Adjoint

/-! The diagram acts on the actual 78-dimensional Geck module and preserves
its integral raising and lowering matrices, with their root parameters fixed. -/
noncomputable section
namespace Atlas.Chevalley.TwistedE6
open E6Data Integral
local instance : Fintype Root := Fintype.ofFinite Root
local instance : InvolutiveNeg Root := pairing.indexNeg

theorem rootDiagram_neg (a : Root) : rootDiagram (-a) = -rootDiagram a :=
  rootDiagram_reflectionPerm a a

theorem rootDiagram_add_eq_iff (a b c : Root) :
    pairing.root (rootDiagram a) = pairing.root (rootDiagram b) + pairing.root (rootDiagram c) ↔
      pairing.root a = pairing.root b + pairing.root c := by
  change latticeDiagram ℤ a.val = latticeDiagram ℤ b.val + latticeDiagram ℤ c.val ↔ _
  rw [← map_add, (latticeDiagram ℤ).injective.eq_iff]
  rfl

theorem rootDiagram_sub_eq_iff (a b c : Root) :
    pairing.root (rootDiagram a) = pairing.root (rootDiagram b) - pairing.root (rootDiagram c) ↔
      pairing.root a = pairing.root b - pairing.root c := by
  change latticeDiagram ℤ a.val = latticeDiagram ℤ b.val - latticeDiagram ℤ c.val ↔ _
  rw [← map_sub, (latticeDiagram ℤ).injective.eq_iff]
  rfl

def adjointIndexDiagram : Equiv.Perm (base.support ⊕ Root) :=
  Equiv.sumCongr baseDiagram rootDiagram

theorem adjointIndexDiagram_involutive : Function.Involutive adjointIndexDiagram := by
  intro a
  cases a with
  | inl i => exact congrArg Sum.inl (baseDiagram_involutive i)
  | inr a => exact congrArg Sum.inr (rootDiagram_involutive a)

theorem diagram_raising_entry (i : base.support) (a c : base.support ⊕ Root) :
    raising pairing base (baseDiagram i) (adjointIndexDiagram a) (adjointIndexDiagram c) =
      raising pairing base i a c := by
  classical
  cases a <;> cases c <;>
    simp only [raising, RootPairing.GeckConstruction.e, adjointIndexDiagram,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
      baseDiagram_root, baseDiagram.injective.eq_iff, ← rootDiagram_neg,
      rootDiagram.injective.eq_iff, baseDiagram_cartan, rootDiagram_chainBot,
      rootDiagram_add_eq_iff] <;> first | rfl | (split <;> simp_all)

theorem diagram_lowering_entry (i : base.support) (a c : base.support ⊕ Root) :
    lowering pairing base (baseDiagram i) (adjointIndexDiagram a) (adjointIndexDiagram c) =
      lowering pairing base i a c := by
  classical
  cases a <;> cases c <;>
    simp only [lowering, RootPairing.GeckConstruction.f, adjointIndexDiagram,
      Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
      baseDiagram_root, baseDiagram.injective.eq_iff, ← rootDiagram_neg,
      rootDiagram.injective.eq_iff, baseDiagram_cartan, rootDiagram_chainTop,
      rootDiagram_sub_eq_iff] <;> first | rfl | (split <;> simp_all)

end Atlas.Chevalley.TwistedE6
