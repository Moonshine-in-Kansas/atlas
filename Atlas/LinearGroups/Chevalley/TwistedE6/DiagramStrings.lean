import Atlas.LinearGroups.Chevalley.TwistedE6.DiagramRoots
import Mathlib.LinearAlgebra.RootSystem.Chain

/-! Preservation of actual root strings by the E6 diagram. This uses the
integral norm shell, not a separately supplied root-string table. -/
namespace Atlas.Chevalley.TwistedE6
open E6Data

theorem root_range_iff (x : Lattice) :
    x ∈ Set.range pairing.root ↔ Atlas.Comparisons.E6Lattice.norm x = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem rootDiagram_independent (a b : Root)
    (h : LinearIndependent ℤ ![pairing.root a, pairing.root b]) :
    LinearIndependent ℤ ![pairing.root (rootDiagram a), pairing.root (rootDiagram b)] := by
  have he : (latticeDiagram ℤ).toLinearMap ∘ ![pairing.root a, pairing.root b] =
      ![pairing.root (rootDiagram a), pairing.root (rootDiagram b)] := by
    funext i
    fin_cases i <;> rfl
  rw [← he]
  exact h.map' (latticeDiagram ℤ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (latticeDiagram ℤ).injective)

theorem rootDiagram_independent_iff (a b : Root) :
    LinearIndependent ℤ ![pairing.root (rootDiagram a), pairing.root (rootDiagram b)] ↔
      LinearIndependent ℤ ![pairing.root a, pairing.root b] := by
  constructor
  · intro h
    simpa only [rootDiagram_involutive a, rootDiagram_involutive b] using
      rootDiagram_independent _ _ h
  · exact rootDiagram_independent a b

theorem rootDiagram_sub_mem (a b : Root) (n : ℕ) :
    pairing.root (rootDiagram b) - n • pairing.root (rootDiagram a) ∈ Set.range pairing.root ↔
      pairing.root b - n • pairing.root a ∈ Set.range pairing.root := by
  rw [root_range_iff, root_range_iff]
  change Atlas.Comparisons.E6Lattice.norm
    (latticeDiagram ℤ b.val - n • latticeDiagram ℤ a.val) = 1 ↔ _
  rw [← map_nsmul, ← map_sub, latticeDiagram_norm]
  rfl

theorem rootDiagram_add_mem (a b : Root) (n : ℕ) :
    pairing.root (rootDiagram b) + n • pairing.root (rootDiagram a) ∈ Set.range pairing.root ↔
      pairing.root b + n • pairing.root a ∈ Set.range pairing.root := by
  rw [root_range_iff, root_range_iff]
  change Atlas.Comparisons.E6Lattice.norm
    (latticeDiagram ℤ b.val + n • latticeDiagram ℤ a.val) = 1 ↔ _
  rw [← map_nsmul, ← map_add, latticeDiagram_norm]
  rfl

theorem rootDiagram_chainBot (a b : Root) :
    pairing.chainBotCoeff (rootDiagram a) (rootDiagram b) = pairing.chainBotCoeff a b := by
  classical
  by_cases h : LinearIndependent ℤ ![pairing.root a, pairing.root b]
  · have hd := rootDiagram_independent a b h
    have he (n : ℕ) : n ≤ pairing.chainBotCoeff (rootDiagram a) (rootDiagram b) ↔
        n ≤ pairing.chainBotCoeff a b := by
      rw [← pairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hd,
        ← pairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, rootDiagram_sub_mem]
    exact Nat.le_antisymm ((he _).mp le_rfl) ((he _).mpr le_rfl)
  · have hd := mt (rootDiagram_independent_iff a b).mp h
    rw [pairing.chainBotCoeff_of_not_linearIndependent hd,
      pairing.chainBotCoeff_of_not_linearIndependent h]

theorem rootDiagram_chainTop (a b : Root) :
    pairing.chainTopCoeff (rootDiagram a) (rootDiagram b) = pairing.chainTopCoeff a b := by
  classical
  by_cases h : LinearIndependent ℤ ![pairing.root a, pairing.root b]
  · have hd := rootDiagram_independent a b h
    have he (n : ℕ) : n ≤ pairing.chainTopCoeff (rootDiagram a) (rootDiagram b) ↔
        n ≤ pairing.chainTopCoeff a b := by
      rw [← pairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hd,
        ← pairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff h, rootDiagram_add_mem]
    exact Nat.le_antisymm ((he _).mp le_rfl) ((he _).mpr le_rfl)
  · have hd := mt (rootDiagram_independent_iff a b).mp h
    rw [pairing.chainTopCoeff_of_not_linearIndependent hd,
      pairing.chainTopCoeff_of_not_linearIndependent h]

end Atlas.Chevalley.TwistedE6
