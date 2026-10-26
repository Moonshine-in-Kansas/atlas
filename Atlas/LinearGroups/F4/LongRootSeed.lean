import Atlas.LinearGroups.F4.G2Embedding
import Atlas.LinearGroups.G2.RootGroups

/-! A concrete long-root seed and independent noncommutativity. The full set of
long-root conjugates and its root-label comparison are separate obligations. -/
noncomputable section
namespace Atlas.F4
variable {F : Type*} [Field F]

def longRootSeed (t : F) : Model F := g2Embedding (Atlas.G2.rootA t)

theorem longRootSeed_add (s t : F) : longRootSeed s * longRootSeed t = longRootSeed (s+t) := by
  rw [longRootSeed, longRootSeed, ← map_mul, Atlas.G2.rootA_add]
  rfl

theorem longRootSeed_injective : Function.Injective (longRootSeed (F := F)) :=
  g2Embedding_injective.comp Atlas.G2.rootA_injective

theorem longRootSeed_apply (t : F) (x : Atlas.Albert.Carrier F) :
    (longRootSeed t).val x = (x.1, fun i => Atlas.G2.Explicit.rootAApply t (x.2 i)) := rfl

/-- Explicit embedded octonion automorphisms witness noncommutativity over every field. -/
theorem exists_mul_ne_mul : ∃ g h : Model F, g*h ≠ h*g := by
  obtain ⟨g,h,he⟩ := Atlas.G2.exists_mul_ne_mul (K := F)
  refine ⟨g2Embedding g,g2Embedding h,?_⟩
  intro hc
  apply he
  apply g2Embedding_injective
  simpa only [map_mul] using hc

end Atlas.F4
