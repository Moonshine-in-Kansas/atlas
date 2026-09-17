import Atlas.Conway.EisensteinGeneratedFrames
import Atlas.Conway.EisensteinConstantFourier
import Atlas.Conway.EisensteinHexadOrbit

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

theorem eisensteinHexadFrame_mem_family (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (i : Fin 12) (hi : i ∈ s) :
    eisensteinHexadFrame s hs i hi ∈ eisensteinHexadFamily := by
  classical
  let p : TernaryConstantHexadPair :=
    ⟨ternaryConstantHexadPair s, Finset.mem_image.mpr ⟨s,hs,rfl⟩⟩
  have he : eisensteinHexadPairFrame p = eisensteinHexadFrame s hs i hi := by
    have hp := eisensteinHexadPairSupport_pair p
    change ternaryConstantHexadPair (eisensteinHexadPairSupport p) =
      ternaryConstantHexadPair s at hp
    rcases (ternaryConstantHexadPair_eq_iff _ _).mp hp with h | h
    · unfold eisensteinHexadPairFrame
      simpa only [h] using
        eisensteinHexadFrame_independent s hs (eisensteinHexadPairPoint p) i
          (by simpa only [h] using eisensteinHexadPairPoint_mem p) hi
    · unfold eisensteinHexadPairFrame
      simpa only [h] using
        (eisensteinHexadFrame_compl s hs i (eisensteinHexadPairPoint p) hi
          (by simpa only [h] using eisensteinHexadPairPoint_mem p)).symm
  apply Finset.mem_biUnion.mpr
  refine ⟨p,Finset.mem_univ _,(eisensteinHexadPairOrbit_mem _ _).mpr ⟨1,?_⟩⟩
  simpa only [map_one,one_smul] using he

theorem eisensteinGeneratedFrames_hexad :
    (eisensteinHexadFamily : Set EisensteinFrame) ⊆ eisensteinGeneratedFrames := by
  have hs : ({0,1,2,3,4,5} : Finset (Fin 12)) ∈ ternaryConstantHexads := by
    apply (mem_ternaryConstantHexads _).mpr
    constructor
    · decide
    · have he : (ternaryGolayEquiv ![1,1,1,1,1,0]).val =
          ternaryTriadWord {0,1,2,3,4,5} := by decide +kernel
      rw [← he]
      exact (ternaryGolayEquiv _).property
  have hF : eisensteinHexadFrame {0,1,2,3,4,5} hs 0 (by decide) ∈
      eisensteinGeneratedFrames := by
    apply (eisensteinGeneratedFrames_fourier_iff _).mp
    rw [eisensteinFourier_hexad_triad]
    exact eisensteinGeneratedFrames_triad (eisensteinTriadFrame_mem_family _ _ _)
  change {G | G ∈ eisensteinHexadFamily} ⊆ eisensteinGeneratedFrames
  rw [← eisensteinHexadFamily_orbit _ (eisensteinHexadFrame_mem_family _ hs 0 (by decide))]
  exact eisensteinGeneratedFrames_localOrbit _ hF

end Atlas.Conway
