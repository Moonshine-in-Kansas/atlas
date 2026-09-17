import Atlas.Fischer.OctadQuadraticClasses
import Atlas.Algebra.BinaryReedMullerHalfWeight

open scoped BigOperators

namespace Atlas.Fischer
open Atlas.Codes Atlas.Algebra

 theorem octadEvenCode_even (O : Octad) (w : octadEvenCode O) : 2 ∣ hammingNorm w.val :=
  even_iff_two_dvd.mp ((even_weight_iff w.val).mpr w.property)

noncomputable def octadEvenHalfWeight (O : Octad) : QuadraticMap Bit (octadEvenCode O) Bit :=
  binaryHalfWeightQuadratic (octadEvenCode O) (octadEvenCode_even O)

theorem octadEvenConstants_radical (O : Octad) : octadEvenConstants O ≤ (octadEvenHalfWeight O).radical := by
  apply Submodule.span_le.mpr
  intro w hw
  have he : w=octadEvenOne O := Set.mem_singleton_iff.mp hw
  rw [he]
  constructor
  · change binaryHalfWeight (octadEvenOne O).val=0
    have h : (octadEvenOne O).val=(fun _ => (1 : Bit)) := funext (octadEvenOne_apply O)
    rw [h]
    simp [binaryHalfWeight,hammingNorm,Fintype.card_coe,octad_size O.val O.property]
  · apply LinearMap.ext
    intro z
    rw [octadEvenHalfWeight,binaryHalfWeightQuadratic_polar]
    change binaryDot (octadEvenOne O).val z.val=0
    have h : (octadEvenOne O).val=(fun _ => (1 : Bit)) := funext (octadEvenOne_apply O)
    rw [h]
    have hz : ∑ i : O.val, z.val i=0 := z.property
    simpa only [binaryDot_apply,one_mul] using hz

/-- Source form q(S)=|S|/2 modulo two on actual even-octad classes. -/
noncomputable def octadClassQuadratic (O : Octad) : QuadraticMap Bit (OctadEvenClasses O) Bit :=
  (octadEvenHalfWeight O).lift (octadEvenConstants O) (octadEvenConstants_radical O)

/-- Half-weight on actual quadratic functions modulo affine functions. -/
noncomputable def binaryQuadraticClassForm : QuadraticMap Bit BinaryQuadraticClasses Bit :=
  binaryReedMullerHalfWeight.lift binaryAffineInQuadratic binaryAffine_halfWeight_radical

@[simp] theorem octadClassQuadratic_mk (O : Octad) (w : octadEvenCode O) :
    octadClassQuadratic O (Submodule.Quotient.mk w)=binaryHalfWeight w.val := rfl

@[simp] theorem binaryQuadraticClassForm_mk (w : binaryQuadraticCode) :
    binaryQuadraticClassForm (Submodule.Quotient.mk w)=binaryHalfWeight w.val := rfl

end Atlas.Fischer
