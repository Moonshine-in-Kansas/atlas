import Atlas.Conway.EisensteinNineHexadFrames
import Atlas.Lattices.EisensteinNineHexadSigns

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices

/-- The two constant-hexad sign families remain distinct under every actual code phase. -/
theorem eisensteinNineHexadFrame_phase_sign (s : Finset (Fin 12))
    (hs : s ∈ ternaryConstantHexads) (k j : Fin 12) (hk : k ∈ s) (hj : j ∉ s)
    (b d : ZMod 3) (hb : b≠0) (hd : d≠0) (t : ternaryGolay)
    (h : eisensteinPhaseIsometries (Multiplicative.ofAdd t) •
        eisensteinNineHexadFrame s hs k j hk hj d hd =
      eisensteinNineHexadFrame s hs k j hk hj b hb) : b=d := by
  rw [eisensteinNineHexadFrame,eisensteinFrameAction_vector] at h
  have hp := congrArg Subtype.val h
  change eisensteinFramePair (eisensteinClass (eisensteinIntegralAction
    (eisensteinPhaseIsometries (Multiplicative.ofAdd t))
      (eisensteinNineHexadLatticeVector s hs k j d))) =
    eisensteinFramePair (eisensteinClass (eisensteinNineHexadLatticeVector s hs k j b)) at hp
  have hy : eisensteinIntegralAction (eisensteinPhaseIsometries (Multiplicative.ofAdd t))
      (eisensteinNineHexadLatticeVector s hs k j d) =
      ⟨eisensteinDiagonal t.val (eisensteinNineHexadVector s k j d),
        eisensteinDiagonal_mem t (eisensteinNineHexadVector_mem s hs k j d)⟩ := by
    apply Subtype.ext
    exact eisensteinIntegralAction_phase t _
  rw [hy,eisensteinFramePair_eq_iff] at hp
  rcases hp with hp|hp
  · exact eisensteinNineHexad_class_sign s hs k j hk hj b d t hp.symm
  · have hn : eisensteinClass (eisensteinNineHexadLatticeVector s hs k j b)=
        -eisensteinClass ⟨eisensteinDiagonal t.val (eisensteinNineHexadVector s k j d),
          eisensteinDiagonal_mem t (eisensteinNineHexadVector_mem s hs k j d)⟩ := by
      rw [hp]; simp
    exact (eisensteinNineHexad_class_not_negative s hs k j hk hj b d t hn).elim

end Atlas.Conway
