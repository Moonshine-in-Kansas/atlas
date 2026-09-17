import Atlas.Fischer.CountingFieldTrace
import Atlas.Fischer.CountingHexacodeComparison
import Atlas.Codes.HexacodeMDS

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

/-- The absolute trace pairing is the retained binary polar form. -/
theorem countingLetter_trace_pair (u v : K) :
    countingFieldTrace (countingLetterEquiv u * countingLetterEquiv v ^ 2)=polar u v := by
  revert u v
  decide

/-- The explicit six local changes of labels preserve the trace pairing. -/
theorem countingHexCoordinates_trace_pair (u v : HexWord) :
    (∑ i : Fin 6, countingFieldTrace (countingHexCoordinates u i *
      countingHexCoordinates v i ^ 2))=wordPolar u v := by
  change (∑ i : Fin 6, countingFieldTrace
    (countingLetterEquiv (countingHexLocal i (u (hexPos i))) *
     countingLetterEquiv (countingHexLocal i (v (hexPos i))) ^ 2))=wordPolar u v
  simp only [countingLetter_trace_pair,KIsometry.map_polar,wordPolar_apply]
  exact Equiv.sum_comp hexIndexEquiv.symm (fun p => polar (u p) (v p))

/-- Binary trace self-orthogonality is transported from the original Golay hexacode. -/
theorem countingHexacode_trace_orthogonal (u v : countingHexacode) :
    (∑ i : Fin 6, countingFieldTrace (u.val i * v.val i ^ 2))=0 := by
  obtain ⟨a,rfl⟩ := countingHexEquiv.surjective u
  obtain ⟨b,rfl⟩ := countingHexEquiv.surjective v
  change (∑ i : Fin 6, countingFieldTrace (countingHexCoordinates a.val i *
      countingHexCoordinates b.val i ^ 2))=0
  rw [countingHexCoordinates_trace_pair]
  have h := wordQ_polar qK qK_polar a.val b.val
  rw [hexacode_isotropic _ (hexacode.add_mem a.property b.property),
    hexacode_isotropic _ a.property,hexacode_isotropic _ b.property] at h
  simpa using h.symm

/-- The pair-complement changes induced by a codeword have even parity. -/
theorem countingHexacode_ratio_trace_even (b g : countingHexacode) :
    (∑ i : Fin 6, countingFieldTrace (b.val i / g.val i))=0 := by
  have hlocal (i : Fin 6) : countingFieldTrace (b.val i / g.val i)=
      countingFieldTrace (b.val i * g.val i ^ 2) := by
    by_cases h : g.val i=0
    · simp [h,countingFieldTrace]
    · exact countingFieldTrace_ratio _ _ h
  simp_rw [hlocal]
  exact countingHexacode_trace_orthogonal b g


/-- Full F4 Hermitian orthogonality, recovered from the two binary trace tests. -/
theorem countingHexacode_hermitian_orthogonal (u v : countingHexacode) :
    (∑ i : Fin 6, u.val i * v.val i ^ 2)=0 := by
  let tr : CountingFour →+ Bit :=
    { toFun := countingFieldTrace, map_zero' := rfl, map_add' := countingFieldTrace_add }
  have h0 : countingFieldTrace (∑ i : Fin 6, u.val i * v.val i ^ 2)=0 := by
    change tr (∑ i : Fin 6, u.val i * v.val i ^ 2)=0
    rw [map_sum]
    exact countingHexacode_trace_orthogonal u v
  have h1 : countingFieldTrace (goldenFourTau * (∑ i : Fin 6, u.val i * v.val i ^ 2))=0 := by
    rw [Finset.mul_sum]
    change tr (∑ i : Fin 6, goldenFourTau * (u.val i * v.val i ^ 2))=0
    rw [map_sum]
    change (∑ i : Fin 6, countingFieldTrace (goldenFourTau * (u.val i * v.val i ^ 2)))=0
    simpa only [Submodule.coe_smul,
      Pi.smul_apply,smul_eq_mul,mul_assoc] using
      countingHexacode_trace_orthogonal (goldenFourTau • u) v
  have hz : ∀ z : CountingFour, countingFieldTrace z=0 →
      countingFieldTrace (goldenFourTau*z)=0 → z=0 := by decide
  exact hz _ h0 h1

end Atlas.Fischer
