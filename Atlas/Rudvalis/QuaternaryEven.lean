import Atlas.Rudvalis.QuaternarySelfDual
import Atlas.Codes.QuaternaryEvenness

/-! Evenness of the literal signed-seed quaternary code. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

theorem quaternaryCode_norm_mod_eight (w : QuaternaryWord) (hw : w∈quaternaryCode) :
    normModEight w=0 := by
  have hle : quaternaryCode≤evenPart quaternaryCode quaternaryCode_self_orthogonal := by
    apply quaternaryCode_le
    · intro b hb
      refine ⟨quaternaryCode_double b hb,?_⟩
      rw [normModEight_double]
      obtain ⟨k,hk⟩ := binaryTorsion_even b hb
      rw [hk]
      push_cast
      ring_nf
      have h8 : (8 : ZMod 8)=0 := by decide
      simp [h8]
    · intro z
      refine ⟨quaternaryCode_seed z,?_⟩
      change normModEight (fun q => (seedOrbitWord z q : Quat))=0
      rw [normModEight_intCast,seedOrbitWord_norm_sq]
      decide
  exact (hle hw).2

theorem quaternaryCode_even (w : QuaternaryWord) (hw : w∈quaternaryCode) :
    8 ∣ euclideanWeight w :=
  (euclideanWeight_even_iff w).mpr (quaternaryCode_norm_mod_eight w hw)

theorem quaternaryCode_integer_norm (v : Coordinate → ℤ)
    (hv : (fun q => (v q : Quat))∈quaternaryCode) : 8 ∣ ∑ q,v q^2 := by
  have h := quaternaryCode_norm_mod_eight (fun q => (v q : Quat)) hv
  rw [normModEight_intCast] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h

end Atlas.Rudvalis
