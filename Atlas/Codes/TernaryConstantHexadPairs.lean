import Atlas.Codes.TernaryConstantHexads
import Atlas.Mathieu.TernaryPhaseAction
import Mathlib.Algebra.Group.Action.Pointwise.Finset

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes
open scoped Pointwise

/-- Complementary constant hexads are the eleven partitions underlying the heavy frames. -/
def ternaryConstantHexadPair (s : Finset (Fin 12)) : Finset (Finset (Fin 12)) := {s,sᶜ}

def ternaryConstantHexadPairs : Finset (Finset (Finset (Fin 12))) :=
  ternaryConstantHexads.image ternaryConstantHexadPair

theorem ternaryConstantHexadPairs_card : ternaryConstantHexadPairs.card = 11 := by
  decide +kernel

theorem ternaryConstantHexadPair_compl (s : Finset (Fin 12)) :
    ternaryConstantHexadPair sᶜ = ternaryConstantHexadPair s := by
  simp [ternaryConstantHexadPair,Finset.pair_comm]

theorem ternaryConstantHexadPair_eq_iff (s t : Finset (Fin 12)) :
    ternaryConstantHexadPair s = ternaryConstantHexadPair t ↔ s=t ∨ s=tᶜ := by
  constructor
  · intro h
    have hs : s ∈ ternaryConstantHexadPair t := by rw [← h]; simp [ternaryConstantHexadPair]
    simpa [ternaryConstantHexadPair] using hs
  · rintro (rfl|rfl)
    · rfl
    · exact ternaryConstantHexadPair_compl t

theorem ternaryFinset_smul (g : TernaryPureAutomorphism) (s : Finset (Fin 12)) :
    g • s = s.map g.val.toEmbedding := by
  change s.image (fun i => g.val i) = s.map g.val.toEmbedding
  rw [Finset.map_eq_image]
  rfl

theorem ternaryConstantHexadPair_smul (g : TernaryPureAutomorphism)
    (s : Finset (Fin 12)) :
    g • ternaryConstantHexadPair s = ternaryConstantHexadPair (g • s) := by
  have he : g • sᶜ = (g • s)ᶜ := by
    rw [ternaryFinset_smul,ternaryFinset_smul]
    ext i; simp
  change (ternaryConstantHexadPair s).image (fun t => g • t) = _
  simp [ternaryConstantHexadPair,he]

theorem ternaryConstantHexadPairs_smul (g : TernaryPureAutomorphism)
    (p : Finset (Finset (Fin 12))) (hp : p ∈ ternaryConstantHexadPairs) :
    g • p ∈ ternaryConstantHexadPairs := by
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hp
  rw [ternaryConstantHexadPair_smul]
  exact Finset.mem_image.mpr ⟨g • s,by
    rw [ternaryFinset_smul]
    exact ternaryConstantHexads_permute g s hs,rfl⟩

abbrev TernaryConstantHexadPair := ↥ternaryConstantHexadPairs

instance : MulAction TernaryPureAutomorphism TernaryConstantHexadPair where
  smul g p := ⟨g • p.val,ternaryConstantHexadPairs_smul g p.val p.property⟩
  one_smul p := Subtype.ext (one_smul _ _)
  mul_smul g h p := Subtype.ext (mul_smul _ _ _)

end Atlas.Codes
