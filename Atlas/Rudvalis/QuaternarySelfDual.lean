import Atlas.Rudvalis.QuaternaryCode
import Atlas.Rudvalis.SeedResidueSpanning
import Atlas.Rudvalis.SeedCorrelations

/-! Self-duality and exact binary layers of the literal signed-seed code. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators

noncomputable def quaternaryResidue : Submodule Bit BinaryWord :=
  AddSubgroup.toZModSubmodule 2 (quaternaryCode.toAddSubgroup.map reduce)

theorem quaternaryResidue_eq : quaternaryResidue=binaryResidue := by
  apply le_antisymm
  · rintro d ⟨q,hq,rfl⟩
    let Q : Submodule (ZMod 4) QuaternaryWord := AddSubgroup.toZModSubmodule 4
      (binaryResidue.toAddSubgroup.comap reduce)
    have hle : quaternaryCode≤Q := quaternaryCode_le Q
      (fun b hb => by change reduce (double b)∈binaryResidue; rw [reduce_double]; exact binaryResidue.zero_mem)
      (fun z => by change reduce (quaternarySeed z)∈binaryResidue
                   rw [quaternarySeed_reduce]; exact seedOrbitResidue_mem z)
    exact hle hq
  · rw [← seedOrbitResidue_span]
    apply Submodule.span_le.mpr
    rintro d ⟨z,rfl⟩
    exact ⟨quaternarySeed z,quaternaryCode_seed z,quaternarySeed_reduce z⟩

theorem quaternaryCode_residue (d : BinaryWord) :
    d∈binaryResidue ↔ ∃ q : QuaternaryWord, q∈quaternaryCode ∧ reduce q=d := by
  rw [← quaternaryResidue_eq]
  rfl

theorem quaternary_even_seed_pair (b : BinaryWord) (hb : b∈binaryTorsion) (z : SeedOrbitIndex) :
    quaternaryForm (double b) (quaternarySeed z)=0 := by
  rw [double_pairing_zero,quaternarySeed_reduce,binaryForm_symmetric]
  exact hb (seedOrbitResidue z) (seedOrbitResidue_mem z)

theorem quaternary_seed_pair (a b : SeedOrbitIndex) :
    quaternaryForm (quaternarySeed a) (quaternarySeed b)=0 := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (∑ z,seedOrbitWord a z*seedOrbitWord b z) 4).mpr (seedOrbitWord_pair_divisible a b)
  simpa [quaternaryForm,quaternarySeed,dotProductBilin,dotProduct,Int.cast_sum,Int.cast_mul] using h

theorem quaternary_pairing_zero_of_generators (w : QuaternaryWord)
    (heven : ∀ b : BinaryWord, b∈binaryTorsion → quaternaryForm w (double b)=0)
    (hseed : ∀ z : SeedOrbitIndex, quaternaryForm w (quaternarySeed z)=0) :
    ∀ u : QuaternaryWord, u∈quaternaryCode → quaternaryForm w u=0 := by
  have hle : quaternaryCode≤(quaternaryForm w).ker :=
    quaternaryCode_le _ heven hseed
  exact fun u hu => hle hu

theorem quaternaryCode_self_orthogonal : quaternaryCode≤quaternaryForm.orthogonal quaternaryCode := by
  apply quaternaryCode_le
  · intro b hb u hu
    rw [quaternaryForm_symmetric]
    exact quaternary_pairing_zero_of_generators (double b)
      (fun c _ => double_double_pairing b c) (quaternary_even_seed_pair b hb) u hu
  · intro z u hu
    rw [quaternaryForm_symmetric]
    exact quaternary_pairing_zero_of_generators (quaternarySeed z)
      (fun b hb => by rw [quaternaryForm_symmetric]; exact quaternary_even_seed_pair b hb z)
      (quaternary_seed_pair z) u hu

theorem quaternaryCode_self_dual : quaternaryForm.orthogonal quaternaryCode=quaternaryCode :=
  selfdual_of_layers quaternaryCode binaryResidue quaternaryCode_residue
    quaternaryCode_self_orthogonal quaternaryCode_double

theorem quaternaryCode_torsion (b : BinaryWord) :
    double b∈quaternaryCode ↔ b∈binaryTorsion :=
  torsion_eq_orthogonal quaternaryCode binaryResidue quaternaryCode_residue
    quaternaryCode_self_orthogonal quaternaryCode_double b

theorem quaternaryCode_card : Nat.card quaternaryCode=2^56 := by
  have h := card_pow_of_layers quaternaryCode binaryResidue quaternaryCode_residue
    quaternaryCode_self_orthogonal quaternaryCode_double
  simpa using h

end Atlas.Rudvalis
