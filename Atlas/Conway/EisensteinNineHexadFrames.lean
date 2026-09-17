import Atlas.Lattices.EisensteinNineHexadVectors
import Atlas.Conway.EisensteinNinePhaseOrbit
import Atlas.Conway.EisensteinHexadPhaseOrbit

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- The actual short vector with six norm-three coordinates and one norm-nine coordinate. -/
def eisensteinNineHexadShellVector (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b : ZMod 3) (hb : b≠0) : EisensteinShell 6 :=
  ⟨eisensteinNineHexadLatticeVector s hs k j b,
    eisensteinNineHexadVector_norm s hs k j hk hj b hb⟩

def eisensteinNineHexadFrame (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b : ZMod 3) (hb : b≠0) : EisensteinFrame :=
  eisensteinFrameOfVector (eisensteinNineHexadShellVector s hs k j hk hj b hb)

local instance eisensteinNineHexadPhaseAction : MulAction (Multiplicative ternaryGolay) EisensteinFrame :=
  MulAction.compHom EisensteinFrame eisensteinPhaseIsometries

/-- Each of the two explicit signs gives an actual phase orbit of243 intrinsic frames. -/
theorem eisensteinNineHexadPhaseOrbit_card (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b : ZMod 3) (hb : b≠0) :
    Nat.card (MulAction.orbit (Multiplicative ternaryGolay)
      (eisensteinNineHexadFrame s hs k j hk hj b hb))=243 := by
  have hn : (-eisensteinPhaseCorrection b).norm=1 := by
    have hf : ∀ a : ZMod 3, a≠0 → (-eisensteinPhaseCorrection a).norm=1 := by decide +kernel
    exact hf b hb
  obtain ⟨a,ha⟩ := (eisenstein_isUnit_iff _).mpr hn
  have hc : eisensteinWordResidue (eisensteinNineHexadLift s k j b)=
      (ternaryConstantHexadCodeword s hs).val.val := by
    funext i
    by_cases hi : i ∈ s <;> simp [eisensteinNineHexadLift,eisensteinWordResidue,
      ternaryConstantHexadCodeword,ternaryTriadWord,hi,
      show eisensteinResidue eisensteinTheta=0 by decide +kernel]
  have hji : j≠k := by intro h; exact hj (h ▸ hk)
  apply eisensteinNine_phase_orbit_card (eisensteinNineHexadShellVector s hs k j hk hj b hb)
    (ternaryConstantHexadCodeword s hs) (eisensteinNineHexadLift s k j b) rfl hc j
    (by simpa only [ternaryConstantHexadCodeword_support] using hj) a
  · rw [ha]
    simp [eisensteinNineHexadLift,hj,hji]
  · intro i hi hij
    rw [ternaryConstantHexadCodeword_support] at hi
    have hik : i≠k := by intro h; exact hi (h ▸ hk)
    simp [eisensteinNineHexadLift,hi,hij,hik]

end Atlas.Conway
