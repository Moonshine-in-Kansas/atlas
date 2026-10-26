import Atlas.Rudvalis.QuaternarySelfDual
import Atlas.Codes.QuaternarySigns

/-! Intrinsic sign patterns of the actual quaternary code. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

noncomputable def signPatterns : Submodule Bit BinaryWord where
  carrier := {s | ∀ d, d∈binaryResidue → (fun z => s z*d z)∈binaryTorsion}
  zero_mem' := by
    intro d hd
    convert binaryTorsion.zero_mem using 1 <;> ext z <;> simp
  add_mem' := by
    intro s t hs ht d hd
    have h := binaryTorsion.add_mem (hs d hd) (ht d hd)
    convert h using 1 <;> ext z <;> simp [add_mul]
  smul_mem' := by
    intro a s hs d hd
    have h := binaryTorsion.smul_mem a (hs d hd)
    convert h using 1 <;> ext z <;> simp [mul_assoc]

theorem signPatterns_iff_preserves (s : BinaryWord) : s∈signPatterns ↔
    ∀ q, q∈quaternaryCode → signChange s q∈quaternaryCode := by
  rw [signs_preserve_iff quaternaryCode binaryResidue quaternaryCode_residue]
  constructor
  · intro hs d hd
    exact (quaternaryCode_torsion _).mpr (hs d hd)
  · intro hs d hd
    exact (quaternaryCode_torsion _).mp (hs d hd)

theorem signPatterns_block_constant (s : BinaryWord) (hs : s∈signPatterns)
    (p : Point) (x : E) : s (p,x)=s (p,0) := by
  classical
  let w : BinaryWord := fun z => s z*rowWord p z
  have hw : w∈binaryTorsion := hs (rowWord p) (binaryResidue_row_word p 1)
  have hb : blockSupported p w := by
    intro q hq y
    simp [w,rowWord,hq]
  have h := binaryTorsion_one_block_constant p w hw hb x
  simpa [w,rowWord] using h

end Atlas.Rudvalis
